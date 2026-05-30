///////////////////////////////////////////////////////////////////////////////
// AUTHOR:       Henry Pinkard, henry.pinkard@gmail.com
//
// COPYRIGHT:    University of California, San Francisco, 2015
//
// LICENSE:      This file is distributed under the BSD license.
//               License text is included with the source distribution.
//
//               This file is distributed in the hope that it will be useful,
//               but WITHOUT ANY WARRANTY; without even the implied warranty
//               of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
//
//               IN NO EVENT SHALL THE COPYRIGHT OWNER OR
//               CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
//               INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES.
//

package org.micromanager.ndtiffstorage;

import java.awt.Point;
import java.io.File;
import java.io.IOException;
import java.nio.Buffer;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import javax.swing.JOptionPane;
import mmcorej.TaggedImage;
import mmcorej.org.json.JSONException;
import mmcorej.org.json.JSONObject;


/**
 * This class manages pyramidal multipage Tiff datasets, averaging multiple 2x2
 * squares of pixels to create successively lower resolutions until the
 * downsample factor is greater or equal to the number of tiles in a given
 * direction. This condition ensures that pixels will always be divisible by the
 * downsample factor without truncation.
 *
 */
public class NDTiffStorage implements NDTiffAPI, MultiresNDTiffAPI {

   public static final ByteOrder BYTE_ORDER = ByteOrder.nativeOrder();

   public static int WRITING_QUEUE_DEFAULT_MAX_SIZE = 50;

   public static final String ROW_AXIS = "row";
   public static final String COL_AXIS = "column";

   // Maximum pyramid level allowed when creating new levels: level 10 = Downsampled_x1024.
   // Prevents runaway pyramid building when the viewer requests an absurdly deep zoom-out.
   // This cap is only enforced when adding new levels; existing on-disk levels deeper than
   // this are loaded without restriction.
   public static final int MAX_RESOLUTION_LEVEL = 10;

   private static final String FULL_RES_SUFFIX = "Full resolution";
   private static final String DOWNSAMPLE_SUFFIX = "Downsampled_x";
   private ResolutionLevel fullResStorage_;
   //map of resolution index to storage instance
   private final TreeMap<Integer, ResolutionLevel> lowResStorages_;
   private final String directory_;
   private final JSONObject summaryMD_;
   private JSONObject displaySettings_;
   private int xOverlap_;
   private int yOverlap_;
   private int fullResTileWidthIncludingOverlap_ = -1;
   private int fullResTileHeightIncludingOverlap_ = -1;
   // Independent of zoom level because tile sizes stay the same--which means overlap is cut off
   private int tileWidth_ = -1;
   private int tileHeight_ = -1;
   private volatile boolean finished_;
   private String uniqueAcqName_;
   private ExecutorService writingExecutor_;
   private volatile int maxResolutionLevel_ = 0;
   private final boolean loaded_;
   private boolean tiled_;
   //this is how to create a concurrent set
   private final Set<HashMap<String, Object>> imageAxes_ =
           new ConcurrentHashMap<HashMap<String, Object>, Boolean>().newKeySet();
   private String prefix_;
   Consumer<String> debugLogger_ = null;
   private LinkedBlockingQueue<Callable<IndexEntryData>> writingTaskQueue_;
   private final HashMap<String, Class> axisTypes_ = new HashMap<>();

   private boolean firstImageAdded_ = false;

   // Per-tile affine position cache, built lazily from level-0 tags.
   // Key = serialized full axes (row+col+non-spatial). Value = full-res (tx, ty) from affine.
   // null = not yet built. Empty = no affine tags present (use uniform grid).
   private volatile Map<String, Point> tileAffinePositions_ = null;
   // Per-level position maps derived from tileAffinePositions_.
   // Key = resolution level. Value = map of serialized level-N axes -> downsampled canvas origin.
   private final Map<Integer, Map<String, Point>> levelPositions_ = new TreeMap<>();
   private final Object affinePositionLock_ = new Object();

   /** Tag name for the per-tile 3D affine transform (row-major 3x4 JSON array). */
   public static final String TILE_AFFINE_TAG = "TileAffineTransform";

   private static final int BUFFER_DIRECT_THRESHOLD = 8192;
   private static final int BUFFER_RECYCLE_SIZE_MIN = 1024;
   private static final int BUFFER_POOL_SIZE =
           System.getProperty("sun.arch.data.model").equals("32") ? 0 : 3;
   private final ConcurrentHashMap<Integer, Deque<ByteBuffer>> pooledBuffers_;
   private int detectedMajorVersion_;
   private volatile Exception writingException_ = null;

   /**
    * Constructor to load existing storage from disk dir --top level saving
    * directory.
    */
   public NDTiffStorage(String dir) throws IOException {
      loaded_ = true;
      directory_ = dir;
      finished_ = true;
      pooledBuffers_ = null;
      lowResStorages_ = new TreeMap<>();

      dir += (dir.endsWith(File.separator) ? "" : File.separator);
      // Differentiate between NDTiff v2 and v3 here.
      if (dir.endsWith(FULL_RES_SUFFIX + File.separator)) {
         // The wrong one was selected
         dir = new File(dir).getParent() + File.separator;
      }

      String fullResDir;
      // First check if there is a "Full resolution" directory present.
      if (! new File(dir + FULL_RES_SUFFIX).exists()) {
         // It must be an NDTiff v3 non-multiresolution
         fullResDir = dir;
         detectedMajorVersion_ = 3;
      } else {
         fullResDir = dir + FULL_RES_SUFFIX;
      }

      //create fullResStorage
      fullResStorage_ = new ResolutionLevel(fullResDir, false, null, this, null);
      summaryMD_ = fullResStorage_.getSummaryMetadata();
      try {
         tiled_ = StorageMD.getTiledStorage(summaryMD_);
      } catch (Exception e) {
         tiled_ = true; //Backwards compat
      }

      try {
         String path = dir + (dir.endsWith(File.separator) ? "" : File.separator)
                 + "display_settings.txt";
         byte[] data = Files.readAllBytes(Paths.get(path));
         displaySettings_ = new JSONObject(new String(data, StandardCharsets.UTF_8));
      } catch (Exception e) {
         System.err.println("Couldn't read displaysettings");
      }

      imageAxes_.addAll(fullResStorage_.imageKeys().stream()
              .map(s -> IndexEntryData.deserializeAxes(s))
              .collect(Collectors.toSet()));

      // Read width from the first image, to allow for datasets with
      // different widths/heights per image
      // Even though this won't be allowed for tiled datasets
      fullResTileHeightIncludingOverlap_ = fullResStorage_.getFirstImageHeight();
      fullResTileWidthIncludingOverlap_ = fullResStorage_.getFirstImageWidth();
      if (tiled_) {
         xOverlap_ = StorageMD.getPixelOverlapX(summaryMD_);
         yOverlap_ = StorageMD.getPixelOverlapY(summaryMD_);

         tileWidth_ = fullResTileWidthIncludingOverlap_ - xOverlap_;
         tileHeight_ = fullResTileHeightIncludingOverlap_ - yOverlap_;
         //create low res storages
         int resIndex = 1;
         while (true) {
            String dsDir = directory_ + (directory_.endsWith(File.separator) ? "" : File.separator)
                    + DOWNSAMPLE_SUFFIX + (1 << resIndex);
            if (!new File(dsDir).exists()) {
               break;
            }
            maxResolutionLevel_ = resIndex;
            lowResStorages_.put(resIndex, new ResolutionLevel(dsDir, false,
                    null, this, null));
            resIndex++;
         }
      } else {
         tileHeight_ = fullResTileHeightIncludingOverlap_;
         tileWidth_ = fullResTileWidthIncludingOverlap_;
      }
   }

   /**
    * Constructor to load an existing dataset from disk in write-append mode,
    * allowing additional resolution levels to be built on demand.
    *
    * @param dir             Path to the existing NDTiff dataset directory
    * @param savingQueueSize Size of the async writing task queue
    * @param debugLogger     Optional debug logger (may be null)
    */
   public NDTiffStorage(String dir, int savingQueueSize, Consumer<String> debugLogger)
           throws IOException {
      loaded_ = true;
      finished_ = false;
      debugLogger_ = debugLogger;
      lowResStorages_ = new TreeMap<>();

      if (BUFFER_POOL_SIZE > 0) {
         pooledBuffers_ = new ConcurrentHashMap<Integer, Deque<ByteBuffer>>();
      } else {
         pooledBuffers_ = null;
      }

      writingExecutor_ = Executors.newSingleThreadExecutor(new ThreadFactory() {
         @Override
         public Thread newThread(Runnable r) {
            return new Thread(r, "Multipage Tiff data writing executor");
         }
      });
      writingTaskQueue_ = new LinkedBlockingQueue<Callable<IndexEntryData>>(savingQueueSize);

      dir += (dir.endsWith(File.separator) ? "" : File.separator);
      if (dir.endsWith(FULL_RES_SUFFIX + File.separator)) {
         dir = new File(dir).getParent() + File.separator;
      }
      // directory_ holds the path without trailing separator, matching the read-only constructor
      directory_ = dir.substring(0, dir.length() - 1);
      // prefix_ is used when creating new resolution-level tiff files
      prefix_ = new File(directory_).getName();

      String fullResDir;
      if (!new File(dir + FULL_RES_SUFFIX).exists()) {
         fullResDir = dir;
         detectedMajorVersion_ = 3;
      } else {
         fullResDir = dir + FULL_RES_SUFFIX;
      }

      fullResStorage_ = new ResolutionLevel(fullResDir, false, null, this, null);
      summaryMD_ = fullResStorage_.getSummaryMetadata();
      try {
         tiled_ = StorageMD.getTiledStorage(summaryMD_);
      } catch (Exception e) {
         tiled_ = true;
      }

      try {
         String path = dir + "display_settings.txt";
         byte[] data = Files.readAllBytes(Paths.get(path));
         displaySettings_ = new JSONObject(new String(data, StandardCharsets.UTF_8));
      } catch (Exception e) {
         // display settings optional
      }

      imageAxes_.addAll(fullResStorage_.imageKeys().stream()
              .map(s -> IndexEntryData.deserializeAxes(s))
              .collect(Collectors.toSet()));

      fullResTileHeightIncludingOverlap_ = fullResStorage_.getFirstImageHeight();
      fullResTileWidthIncludingOverlap_ = fullResStorage_.getFirstImageWidth();
      if (tiled_) {
         xOverlap_ = StorageMD.getPixelOverlapX(summaryMD_);
         yOverlap_ = StorageMD.getPixelOverlapY(summaryMD_);
         tileWidth_ = fullResTileWidthIncludingOverlap_ - xOverlap_;
         tileHeight_ = fullResTileHeightIncludingOverlap_ - yOverlap_;
         // Load existing low-res storages so they are not overwritten when new levels are added
         int resIndex = 1;
         while (true) {
            String dsDir = directory_ + (directory_.endsWith(File.separator) ? "" : File.separator)
                    + DOWNSAMPLE_SUFFIX + (1 << resIndex);
            File dsDirFile = new File(dsDir);
            if (!dsDirFile.exists()) {
               break;
            }
            try {
               lowResStorages_.put(resIndex, new ResolutionLevel(dsDir, false, null, this, null));
               maxResolutionLevel_ = resIndex;
            } catch (Exception e) {
               // Incomplete or corrupt downsample directory; stop here — will be rebuilt on demand
               break;
            }
            resIndex++;
         }
      } else {
         tileHeight_ = fullResTileHeightIncludingOverlap_;
         tileWidth_ = fullResTileWidthIncludingOverlap_;
      }
   }

   /**
    * Constructor for new storage that doesn't parse summary metadata.
    */
   public NDTiffStorage(String dir, String name, JSONObject summaryMetadata,
                        int overlapX, int overlapY, boolean tiled,
                        Integer externalMaxResLevel, int savingQueueSize,
                        Consumer<String> debugLogger, boolean createDir) {
      tiled_ = tiled;
      xOverlap_ = overlapX;
      yOverlap_ = overlapY;
      prefix_ = name;
      debugLogger_ = debugLogger;
      lowResStorages_ = new TreeMap<>();

      if (BUFFER_POOL_SIZE > 0) {
         pooledBuffers_ = new ConcurrentHashMap<Integer, Deque<ByteBuffer>>();
      } else {
         pooledBuffers_ = null;
      }

      loaded_ = false;
      writingExecutor_ = Executors.newSingleThreadExecutor(new ThreadFactory() {
         @Override
         public Thread newThread(Runnable r) {
            return new Thread(r, "Multipage Tiff data writing executor");
         }
      });

      writingTaskQueue_ = new LinkedBlockingQueue<Callable<IndexEntryData>>(savingQueueSize);


      try {
         //make a copy in case tag changes are needed later
         summaryMD_ = new JSONObject(summaryMetadata.toString());
         if (tiled) {
            StorageMD.setPixelOverlapX(summaryMD_, xOverlap_);
            StorageMD.setPixelOverlapY(summaryMD_, yOverlap_);
         }
         StorageMD.setTiledStorage(summaryMD_, tiled_);
      } catch (JSONException ex) {
         throw new RuntimeException("Couldnt copy summary metadata");
      }

      try {
         if (!createDir) {
            //  In MM MDAs, top level dir is created by other code
            directory_ = dir;
         } else {
            uniqueAcqName_ = getUniqueAcqDirName(dir, name);
            //create acqusition directory for actual data
            directory_ = dir + (dir.endsWith(File.separator) ? "" : File.separator) + uniqueAcqName_;
         }

      } catch (Exception e) {
         throw new RuntimeException("Couldn't make acquisition directory");
      }

      Future f = blockingWritingTaskHandoff(new Callable<IndexEntryData>() {
         @Override
         public IndexEntryData call() {
            //create directory for full res data
            String fullResDir;
            if (tiled_) {
               fullResDir = directory_ + (dir.endsWith(File.separator) ? "" : File.separator) + FULL_RES_SUFFIX;
            } else {
               fullResDir = directory_;
            }
            try {
               createDir(fullResDir);
            } catch (Exception ex) {
               throw new RuntimeException("couldn't create saving directory");
            }

            try {
               //Create full Res storage
               fullResStorage_ = new ResolutionLevel(fullResDir, true, summaryMD_,
                       NDTiffStorage.this, prefix_);
            } catch (IOException ex) {
               throw new RuntimeException("couldn't create Full res storage");
            }
            return null;
         }
      });
      // Wait until the storage initialization is complete to prevent a race condition
      try {
         f.get();
      } catch (Exception e) {
         throw new RuntimeException("Couldn't initialize storage");
      }
   }

   static File createDir(String dir) {
      File dirrr = new File(dir);
      if (!dirrr.exists()) {
         if (!dirrr.mkdirs()) {
            JOptionPane.showMessageDialog(null, "Couldn't create directory " + dir);
            throw new RuntimeException("Unable to create directory " + dir);
         }
      }
      return dirrr;
   }

   public void setDisplaySettings(JSONObject displaySettings) {
      try {
         displaySettings_ = new JSONObject(displaySettings.toString());
      } catch (JSONException e) {
         throw new RuntimeException(e);
      }
   }

   public String getUniqueAcqName() {
      return uniqueAcqName_ + ""; //make new instance
   }

   @Override
   public int getWritingQueueTaskSize() {
      return writingTaskQueue_.size();
   }

   @Override
   public int getWritingQueueTaskMaxSize() {
      return writingTaskQueue_.remainingCapacity() + writingTaskQueue_.size();
   }

   public int getNumResLevels() {
      return maxResolutionLevel_ + 1;
   }

   public int[] getImageBounds() {
      if (!tiled_) {
         return new int[]{0, 0, fullResTileWidthIncludingOverlap_, fullResTileHeightIncludingOverlap_};
      }
      if (tileWidth_ == -1 || tileHeight_ == -1) {
         return null;
      }
      if (!loaded_) {
         return new int[]{0, 0, (int) ((getMinCol() + getNumCols()) * tileWidth_),
                 (int) ((getMinRow() + getNumRows()) * tileHeight_)};
      } else {
         int yMin = (int) (getMinRow() * tileHeight_);
         int xMin = (int) (getMinCol() * tileWidth_);
         int xMax = (int) (getNumCols() * tileWidth_ + xMin);
         int yMax = (int) (getNumRows() * tileHeight_ + yMin);
         return new int[]{xMin, yMin, xMax, yMax};
      }
   }

   private int getNumRows() {
      if (imageAxes_.isEmpty()) {
         return 1;
      }
      int maxRow = imageAxes_.stream().mapToInt(value -> (Integer) value.get(ROW_AXIS)).max().getAsInt();
      int minRow = imageAxes_.stream().mapToInt(value -> (Integer) value.get(ROW_AXIS)).min().getAsInt();
      return 1 + maxRow - minRow;
   }

   private int getNumCols() {
      if (imageAxes_.isEmpty()) {
         return 1;
      }
      int maxCol = imageAxes_.stream().mapToInt(value -> (Integer) value.get(COL_AXIS)).max().getAsInt();
      int minCol = imageAxes_.stream().mapToInt(value -> (Integer) value.get(COL_AXIS)).min().getAsInt();
      return 1 + maxCol - minCol;
   }

   /**
    * Builds the per-tile affine position cache from level-0 tile tags (run once, synchronized).
    * Reads TileAffineTransform (3x4 row-major array) or falls back to XPositionPix/YPositionPix.
    * If any tile lacks both, sets an empty map so the uniform-grid path is used.
    */
   private void ensureTileAffinePositions() {
      if (tileAffinePositions_ != null) {
         return;
      }
      synchronized (affinePositionLock_) {
         if (tileAffinePositions_ != null) {
            return;
         }
         if (!tiled_ || imageAxes_.isEmpty()) {
            tileAffinePositions_ = new HashMap<>();
            return;
         }
         Map<String, Point> positions = new HashMap<>();
         for (HashMap<String, Object> axes : imageAxes_) {
            String key = IndexEntryData.serializeAxes(axes);
            TaggedImage ti = fullResStorage_.getImage(key);
            if (ti == null || ti.tags == null) {
               positions = new HashMap<>();
               break;
            }
            int tx;
            int ty;
            mmcorej.org.json.JSONArray affineArr = ti.tags.optJSONArray(TILE_AFFINE_TAG);
            if (affineArr != null && affineArr.length() == 12) {
               tx = (int) Math.round(affineArr.optDouble(3, Double.NaN));
               ty = (int) Math.round(affineArr.optDouble(7, Double.NaN));
               if (Double.isNaN(affineArr.optDouble(3, Double.NaN))) {
                  positions = new HashMap<>();
                  break;
               }
            } else {
               int xp = ti.tags.optInt("XPositionPix", Integer.MIN_VALUE);
               int yp = ti.tags.optInt("YPositionPix", Integer.MIN_VALUE);
               if (xp == Integer.MIN_VALUE || yp == Integer.MIN_VALUE) {
                  positions = new HashMap<>();
                  break;
               }
               tx = xp;
               ty = yp;
            }
            positions.put(key, new Point(tx, ty));
         }
         tileAffinePositions_ = positions;
      }
   }

   /**
    * Returns the canvas origin (in level-dsIndex pixel coords) for the tile identified
    * by axesCopy (which must include ROW_AXIS and COL_AXIS).
    * Only valid when tileAffinePositions_ is non-empty.
    */
   private Point getAffineBoundsAtLevel(HashMap<String, Object> axesCopy, int dsIndex) {
      synchronized (affinePositionLock_) {
         Map<String, Point> levelMap = levelPositions_.get(dsIndex);
         if (levelMap == null) {
            levelMap = buildLevelPositionMap(dsIndex);
            levelPositions_.put(dsIndex, levelMap);
         }
         String key = IndexEntryData.serializeAxes(axesCopy);
         return levelMap.get(key);
      }
   }

   /** Builds the level-N canvas origin map from the full-res position map. */
   private Map<String, Point> buildLevelPositionMap(int dsIndex) {
      Map<String, Point> levelMap = new HashMap<>();
      for (Map.Entry<String, Point> e : tileAffinePositions_.entrySet()) {
         levelMap.put(e.getKey(), e.getValue());
      }
      return levelMap;
   }

   /*
    * It does not matter what resolution level the pixel is at since tiles
    * are the same size at every level.
    */
   private long tileIndexFromPixelIndex(long i, boolean xDirection) {
      if (i >= 0) {
         return i / (xDirection ? tileWidth_ : tileHeight_);
      } else {
         //highest pixel is -1 for tile indexed -1, so need to add one to pixel values before dividing
         return (i + 1) / (xDirection ? tileWidth_ : tileHeight_) - 1;
      }
   }

   /**
    * @param dsIndex
    * @return
    */
   private boolean hasImage(int dsIndex, HashMap<String, Object> axes) {
      ResolutionLevel storage;
      if (dsIndex == 0) {
         storage = fullResStorage_;
      } else {
         if (lowResStorages_.get(dsIndex) == null) {
            return false;
         }
         storage = lowResStorages_.get(dsIndex);
      }

      return storage.hasImage(IndexEntryData.serializeAxes(axes));
   }


   /**
    * Returns a subimage of the larger stitched image at the appropriate zoom
    * level, loading only the tiles needed to form the subimage.
    *
    * @param axes
    * @param dsIndex 0 for full res, 1 for 2x downsample, 2 for 4x downsample,
    * etc..
    * @param x coordinate of leftmost pixel in requested resolution
    * @param y coordinate of topmost pixel in requested resolution
    * @param width pixel width of image at requested resolution
    * @param height pixel height of image at requested resolution
    * @return Tagged image or taggeded image with background pixels and null
    * tags if no pixel data is present
    */
   public TaggedImage getDisplayImage(HashMap<String, Object> axes,
                                      int dsIndex, int x, int y, int width, int height) {
      ensureTileAffinePositions();
      boolean useAffine = tiled_ && !tileAffinePositions_.isEmpty();
      if (useAffine) {
         return getDisplayImageWithAffinePositions(axes, dsIndex, x, y, width, height);
      }
      return getDisplayImageUniformGrid(axes, dsIndex, x, y, width, height);
   }

   /**
    * Original uniform-grid implementation of getDisplayImage (unchanged behaviour).
    */
   private TaggedImage getDisplayImageUniformGrid(HashMap<String, Object> axes,
                                                   int dsIndex, int x, int y,
                                                   int width, int height) {
      // Figure out what type of pixels
      Object pixels = null;
      //go line by line through one column of tiles at a time, then move to next column
      JSONObject topLeftMD = null;
      //first calculate how many columns and rows of tiles are relevant and the number of pixels
      //of each tile to copy into the returned image
      long previousCol = tileIndexFromPixelIndex(x, true) - 1; //make it one less than the first col in loop
      LinkedList<Integer> lineWidths = new LinkedList<Integer>();
      for (long i = x; i < x + width; i++) { //Iterate through every column of pixels in the image to be returned
         long colIndex = tileIndexFromPixelIndex(i, true);
         if (colIndex != previousCol) {
            lineWidths.add(0);
         }
         //Increment current width
         lineWidths.add(lineWidths.removeLast() + 1);
         previousCol = colIndex;
      }
      //do the same thing for rows
      long previousRow = tileIndexFromPixelIndex(y, false) - 1; //one less than first row in loop?
      LinkedList<Integer> lineHeights = new LinkedList<Integer>();
      for (long i = y; i < y + height; i++) {
         long rowIndex = tileIndexFromPixelIndex(i, false);
         if (rowIndex != previousRow) {
            lineHeights.add(0);
         }
         //add one to pixel count of current height
         lineHeights.add(lineHeights.removeLast() + 1);
         previousRow = rowIndex;
      }
      //get starting row and column
      long rowStart = tileIndexFromPixelIndex(y, false);
      long colStart = tileIndexFromPixelIndex(x, true);
      //xOffset and y offset are the distance from the top left of the display image into which
      //we are copying data
      int xOffset = 0;
      for (long col = colStart; col < colStart + lineWidths.size(); col++) {
         int yOffset = 0;
         for (long row = rowStart; row < rowStart + lineHeights.size(); row++) {
            HashMap<String, Object> axesCopy = IndexEntryData.deserializeAxes(
                  IndexEntryData.serializeAxes(axes));
            //Add in axes for row and col because this is how tiles are stored
            if (tiled_) {
               axesCopy.put(ROW_AXIS, (int) row);
               axesCopy.put(COL_AXIS, (int) col);
            }
            TaggedImage tile = getImage(axesCopy, dsIndex);
            if (tile == null) {
               yOffset += lineHeights.get((int) (row - rowStart));
               continue;
            } else if ((tile.pix instanceof byte[] && ((byte[]) tile.pix).length == 0)
                    || (tile.pix instanceof short[] && ((short[]) tile.pix).length == 0)) {
               yOffset += lineHeights.get((int) (row - rowStart));
               continue;
            }
            if (topLeftMD == null) {
               topLeftMD = tile.tags;
            }
            for (int line = yOffset; line < lineHeights.get((int) (row - rowStart)) + yOffset;
                  line++) {
               int tileYPix = (int) ((y + line) % tileHeight_);
               int tileXPix = (int) ((x + xOffset) % tileWidth_);
               while (tileXPix < 0) {
                  tileXPix += tileWidth_;
               }
               while (tileYPix < 0) {
                  tileYPix += tileHeight_;
               }
               try {
                  EssentialImageMetadata eimd = getEssentialImageMetadata(axesCopy, dsIndex);
                  if (pixels == null) {
                     if (eimd.rgb) {
                        pixels = new byte[width * height * 4];
                     } else if (tile.pix instanceof byte[]) {
                        pixels = new byte[width * height];
                     } else {
                        pixels = new short[width * height];
                     }
                  }
                  int multiplier = eimd.rgb ? 4 : 1;
                  if (dsIndex == 0) {
                     tileYPix += yOverlap_ / 2;
                     tileXPix += xOverlap_ / 2;
                     System.arraycopy(tile.pix, multiplier * (tileYPix
                             * fullResTileWidthIncludingOverlap_ + tileXPix),
                             pixels, (xOffset + width * line) * multiplier,
                             multiplier * lineWidths.get((int) (col - colStart)));
                  } else {
                     System.arraycopy(tile.pix, multiplier * (tileYPix * tileWidth_
                             + tileXPix), pixels, multiplier * (xOffset + width * line),
                             multiplier * lineWidths.get((int) (col - colStart)));
                  }
               } catch (Exception e) {
                  e.printStackTrace();
                  throw new RuntimeException("Problem copying pixels");
               }
            }
            yOffset += lineHeights.get((int) (row - rowStart));
         }
         xOffset += lineWidths.get((int) (col - colStart));
      }
      return new TaggedImage(pixels, topLeftMD);
   }

   /**
    * Position-aware implementation of getDisplayImage.
    * Uses per-tile TileAffineTransform / XPositionPix origins instead of the uniform grid.
    * Iterates all tiles whose affine origin overlaps the requested viewport rectangle.
    */
   private TaggedImage getDisplayImageWithAffinePositions(HashMap<String, Object> axes,
                                                           int dsIndex,
                                                           int x, int y,
                                                           int width, int height) {
      Object pixels = null;
      JSONObject topLeftMD = null;
      EssentialImageMetadata eimd = null;

      if (dsIndex == 0) {
         // Level 0: iterate full-res tiles, place each at its affine canvas position.
         // Buffer pixel (0,0) = canvas (tx, ty); buffer is fullResTileWidthIncludingOverlap_ wide.
         for (String levelKey : fullResStorage_.imageKeys()) {
            HashMap<String, Object> tileAxes = IndexEntryData.deserializeAxes(levelKey);
            if (!matchesNonSpatialAxes(axes, tileAxes)) {
               continue;
            }
            Point origin = getAffineBoundsAtLevel(tileAxes, 0);
            if (origin == null) {
               continue;
            }
            int tileX0 = origin.x;
            int tileY0 = origin.y;
            int tileX1 = tileX0 + fullResTileWidthIncludingOverlap_;
            int tileY1 = tileY0 + fullResTileHeightIncludingOverlap_;
            if (tileX1 <= x || tileX0 >= x + width || tileY1 <= y || tileY0 >= y + height) {
               continue;
            }
            TaggedImage tile = fullResStorage_.getImage(levelKey);
            if (tile == null || tile.pix == null || isEmptyPix(tile.pix)) {
               continue;
            }
            if (topLeftMD == null) {
               topLeftMD = tile.tags;
            }
            if (eimd == null) {
               eimd = getEssentialImageMetadata(tileAxes, 0);
               if (eimd == null) {
                  continue;
               }
               pixels = allocatePixels(pixels, width, height, eimd, tile);
            }
            int multiplier = eimd.rgb ? 4 : 1;
            int storedW = fullResTileWidthIncludingOverlap_;
            int intX0 = Math.max(tileX0, x);
            int intY0 = Math.max(tileY0, y);
            int intX1 = Math.min(tileX1, x + width);
            int intY1 = Math.min(tileY1, y + height);
            for (int row = intY0; row < intY1; row++) {
               int srcIdx = multiplier * ((row - tileY0) * storedW + (intX0 - tileX0));
               int dstIdx = multiplier * ((row - y) * width + (intX0 - x));
               int copyLen = Math.min(multiplier * (intX1 - intX0),
                     multiplier * (storedW - (intX0 - tileX0)));
               try {
                  System.arraycopy(tile.pix, srcIdx, pixels, dstIdx, copyLen);
               } catch (Exception e) {
                  e.printStackTrace();
                  throw new RuntimeException("Problem copying pixels at level 0");
               }
            }
         }
         return new TaggedImage(pixels, topLeftMD);
      }

      // Level N >= 1: the level-N buffer packs dsScale×dsScale full-res tiles into quadrants.
      // Each full-res tile at (fullRow, fullCol) occupies quadrant
      //   (xPos = fullCol % dsScale, yPos = fullRow % dsScale)
      // inside its level-N tile at (fullRow >> dsIndex, fullCol >> dsIndex).
      // The quadrant's buffer region is:
      //   x: [xPos * quadW, (xPos+1) * quadW)   where quadW = tileWidth_ / dsScale
      //   y: [yPos * quadH, (yPos+1) * quadH)   where quadH = tileHeight_ / dsScale
      // The downsample code (resolutionIndex==1) reads from level-0 buffer at
      //   pixelX = x + xOverlap_/2,  where x iterates 0..tileWidth_-1 step 2
      // so buffer pixel (bx, by) at level N >= 1 corresponds to full-res content pixel
      //   (bx*2 + xOverlap_/2 at level 1, etc.) — but for placement purposes:
      // The quadrant's canvas position = (tx + xOverlap_/2) / dsScale for the contributing
      // full-res tile, where tx is the TileAffineTransform origin.
      //
      // Strategy: iterate full-res tiles (which have affine positions), compute which
      // level-N tile they contribute to, fetch that level-N tile's buffer, and blit the
      // quadrant region mapping canvas coords to buffer offsets.

      int dsScale = 1 << dsIndex;
      int quadW = tileWidth_ / dsScale;   // width of one quadrant in the level-N buffer
      int quadH = tileHeight_ / dsScale;

      ResolutionLevel dsStorage = lowResStorages_.get(dsIndex);
      if (dsStorage == null) {
         return new TaggedImage(null, null);
      }

      for (HashMap<String, Object> fullResAxes : imageAxes_) {
         if (!matchesNonSpatialAxes(axes, fullResAxes)) {
            continue;
         }
         Object rowObj = fullResAxes.get(ROW_AXIS);
         Object colObj = fullResAxes.get(COL_AXIS);
         if (!(rowObj instanceof Integer) || !(colObj instanceof Integer)) {
            continue;
         }
         int fullRow = (Integer) rowObj;
         int fullCol = (Integer) colObj;

         // Canvas position of this full-res tile's content at level N.
         String fullKey = IndexEntryData.serializeAxes(fullResAxes);
         Point fullPos = tileAffinePositions_.get(fullKey);
         if (fullPos == null) {
            continue;
         }
         // Quadrant buffer pixel 0 = full-res content pixel 0 = canvas (tx + xOverlap_/2)/dsScale.
         int canvasX0 = (fullPos.x + xOverlap_ / 2) / dsScale;
         int canvasY0 = (fullPos.y + yOverlap_ / 2) / dsScale;
         int canvasX1 = canvasX0 + quadW;
         int canvasY1 = canvasY0 + quadH;

         // Skip if this region doesn't intersect the viewport.
         if (canvasX1 <= x || canvasX0 >= x + width || canvasY1 <= y || canvasY0 >= y + height) {
            continue;
         }

         // Fetch the level-N tile that contains this full-res tile's quadrant.
         int levelRow = Math.floorDiv(fullRow, dsScale);
         int levelCol = Math.floorDiv(fullCol, dsScale);
         int xPos = Math.floorMod(fullCol, dsScale);
         int yPos = Math.floorMod(fullRow, dsScale);

         HashMap<String, Object> levelAxes = new HashMap<>(fullResAxes);
         levelAxes.put(ROW_AXIS, levelRow);
         levelAxes.put(COL_AXIS, levelCol);
         String levelKey = IndexEntryData.serializeAxes(levelAxes);

         TaggedImage tile = dsStorage.getImage(levelKey);
         if (tile == null || tile.pix == null || isEmptyPix(tile.pix)) {
            continue;
         }
         if (topLeftMD == null) {
            topLeftMD = tile.tags;
         }
         if (eimd == null) {
            eimd = getEssentialImageMetadata(levelAxes, dsIndex);
            if (eimd == null) {
               continue;
            }
            pixels = allocatePixels(pixels, width, height, eimd, tile);
         }

         int multiplier = eimd.rgb ? 4 : 1;
         // The quadrant for this full-res tile starts at (bufQX0, bufQY0) in the level-N buffer.
         int bufQX0 = xPos * quadW;
         int bufQY0 = yPos * quadH;

         // Intersection of this tile's canvas region with the viewport.
         int intX0 = Math.max(canvasX0, x);
         int intY0 = Math.max(canvasY0, y);
         int intX1 = Math.min(canvasX1, x + width);
         int intY1 = Math.min(canvasY1, y + height);

         for (int row = intY0; row < intY1; row++) {
            int bufY = bufQY0 + (row - canvasY0);
            if (bufY < bufQY0) bufY = bufQY0;
            else if (bufY >= bufQY0 + quadH) bufY = bufQY0 + quadH - 1;
            if (bufY < 0 || bufY >= tileHeight_) continue;

            // Main copy: in-bounds canvas pixels map 1:1 to buffer pixels.
            int clampedIntX0 = Math.max(intX0, canvasX0);
            int clampedIntX1 = Math.min(intX1, canvasX1);
            if (clampedIntX1 > clampedIntX0) {
               int bufX = bufQX0 + (clampedIntX0 - canvasX0);
               int srcIdx = multiplier * (bufY * tileWidth_ + bufX);
               int dstIdx = multiplier * ((row - y) * width + (clampedIntX0 - x));
               int copyLen = multiplier * (clampedIntX1 - clampedIntX0);
               try {
                  System.arraycopy(tile.pix, srcIdx, pixels, dstIdx, copyLen);
               } catch (Exception e) {
                  e.printStackTrace();
                  throw new RuntimeException("Problem copying pixels at level " + dsIndex);
               }
            }
            // Edge pixel: write canvas pixel canvasX1 using the last buffer pixel.
            // Covers 1-pixel rounding gaps from integer division in canvasX0/canvasX1.
            if (canvasX1 >= x && canvasX1 < x + width) {
               int edgeBufX = bufQX0 + quadW - 1;
               int edgeSrcIdx = multiplier * (bufY * tileWidth_ + edgeBufX);
               int edgeDstIdx = multiplier * ((row - y) * width + (canvasX1 - x));
               try {
                  System.arraycopy(tile.pix, edgeSrcIdx, pixels, edgeDstIdx, multiplier);
               } catch (Exception e) {
                  e.printStackTrace();
                  throw new RuntimeException("Problem edge-pixel at level " + dsIndex);
               }
            }
         }
      }
      return new TaggedImage(pixels, topLeftMD);
   }

   private boolean matchesNonSpatialAxes(HashMap<String, Object> requested,
                                          HashMap<String, Object> candidate) {
      for (Map.Entry<String, Object> e : requested.entrySet()) {
         String k = e.getKey();
         if (k.equals(ROW_AXIS) || k.equals(COL_AXIS)) {
            continue;
         }
         if (!e.getValue().equals(candidate.get(k))) {
            return false;
         }
      }
      return true;
   }

   private boolean isEmptyPix(Object pix) {
      if (pix instanceof byte[]) {
         return ((byte[]) pix).length == 0;
      }
      if (pix instanceof short[]) {
         return ((short[]) pix).length == 0;
      }
      return false;
   }

   private Object allocatePixels(Object existing, int width, int height,
                                  EssentialImageMetadata eimd, TaggedImage tile) {
      if (existing != null) {
         return existing;
      }
      if (eimd.rgb) {
         return new byte[width * height * 4];
      } else if (tile.pix instanceof byte[]) {
         return new byte[width * height];
      } else {
         return new short[width * height];
      }
   }

   /**
    * Down-samples previousLevelPix into currentLevelPix, averaging 2x2 squares
    * of pixels to create the down-sampled image.
    *
    * @param currentLevelPix pixels at current resolution level
    * @param previousLevelPix pixels at previous resolution level
    * @param previousLevelRow row of previous level imagel
    * @param previousLevelCol column of previous level image
    * @param resolutionIndex Only used to see if we are at the highest resolution.
    * @param rgb Where this is an rgb image
    */
   private void downsample(Object currentLevelPix, Object previousLevelPix, int previousLevelRow,
                           int previousLevelCol, int resolutionIndex,
                           boolean rgb) {
      int byteDepth = currentLevelPix instanceof byte[] ? 1 : 2;
      //Determine which position in 2x2 this tile sits in
      int xPos = Math.abs(previousLevelCol % 2);
      int yPos = Math.abs(previousLevelRow % 2);
      //Add one if top or left so border pixels from an odd length image gets added in
      for (int x = 0; x < tileWidth_; x += 2) { //iterate over previous res level pixels
         for (int y = 0; y < tileHeight_; y += 2) {
            //average a square of 4 pixels from previous level
            //edges: if odd number of pixels in tile, round to determine which
            //tiles pixels make it to next res level

            //these are the indices of pixels at the previous res level, which are offset
            //when moving from res level 0 to one as we throw away the overlapped image edges
            int pixelX, pixelY, previousLevelWidth, previousLevelHeight;
            if (resolutionIndex == 1) {
               //add offsets to account for overlap pixels at resolution level 0
               pixelX = x + xOverlap_ / 2;
               pixelY = y + yOverlap_ / 2;
               previousLevelWidth = fullResTileWidthIncludingOverlap_;
               previousLevelHeight = fullResTileHeightIncludingOverlap_;
            } else {
               pixelX = x;
               pixelY = y;
               previousLevelWidth = tileWidth_;
               previousLevelHeight = tileHeight_;

            }
            int rgbMultiplier = rgb ? 4 : 1;
            for (int compIndex = 0; compIndex < (rgb ? 4 : 1); compIndex++) {
               //count is number of pixels (out of 4) used to create a pixel at this level
               int count = 1;
               //always take top left pixel, maybe take others depending on whether at image edge
               int sum = 0;
               if (rgb) {
                  sum += ((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX)
                          * rgbMultiplier + compIndex] & 0xff;
               } else if (byteDepth == 1) {
                  sum += ((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX)] & 0xff;
               } else {
                  sum += ((short[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX)]
                          & 0xffff;
               }

               // pixel index can be different from index in tile at resolution level 0
               // if there is nonzero overlap.
               if (x < previousLevelWidth - 1 && y < previousLevelHeight - 1) {
                  //if not bottom right corner, add three more pix
                  count += 3;
                  if (rgb) {
                     sum += (((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX + 1) * rgbMultiplier + compIndex] & 0xff)
                             + (((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1) * rgbMultiplier + compIndex] & 0xff)
                             + (((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) * rgbMultiplier + compIndex] & 0xff);
                  } else if (byteDepth == 1) {
                     sum += (((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX + 1)  ] & 0xff)
                             + (((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1)  ] & 0xff)
                             + (((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX)  ] & 0xff);
                  } else {
                     sum += (((short[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX + 1)  ] & 0xffff)
                             + (((short[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1)  ] & 0xffff)
                             + (((short[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX)  ] & 0xffff);
                  }
               } else if (x < previousLevelWidth - 1) { //if not right edge, add one more pix
                  count++;
                  if (rgb) {
                     sum += ((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1) * rgbMultiplier + compIndex] & 0xff;
                  } else if (byteDepth == 1) {
                     sum += ((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1)  ] & 0xff;
                  } else {
                     sum += ((short[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1)  ] & 0xffff;
                  }
               } else if (y < previousLevelHeight - 1) { // if not bottom edge, add one more pix
                  count++;
                  if (rgb) {
                     sum += ((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) * rgbMultiplier + compIndex] & 0xff;
                  } else if (byteDepth == 1) {
                     sum += ((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) ] & 0xff;
                  } else {
                     sum += ((short[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) ] & 0xffff;
                  }
               } else {
                  //it is the bottom right corner, no more pix to add
               }
               //add averaged pixel into appropriate quadrant of current res level
               //if full res tile has an odd number of pix, the last one gets chopped off
               //to make it fit into tile containers
               try {
                  int index = (((y + yPos * tileHeight_) / 2) * tileWidth_
                          + (x + xPos * tileWidth_) / 2) * (rgb ? rgbMultiplier : 1)
                          + compIndex;
                  if (byteDepth == 1 || rgb) {
                     // this looks suspicious....
                     ((byte[]) currentLevelPix)[index] = (byte) Math.round(sum / count);
                  } else {
                     // this looks suspicious....
                     ((short[]) currentLevelPix)[index] = (short) Math.round(sum / count);
                  }
               } catch (Exception e) {
                  e.printStackTrace();
                  throw new RuntimeException("Couldn't copy pixels to lower resolution");
               }

            }
         }
      }
   }

   private void populateNewResolutionLevel(int resolutionIndex, boolean addToLowResStorage) {
      // could be accessed from UI or from data arriving
      if (!lowResStorages_.containsKey(resolutionIndex)) {
         createDownsampledStorage(resolutionIndex);
      }

      if (addToLowResStorage) {
         //add all tiles from existing resolution levels to this new one
         ResolutionLevel previousLevelStorage
                 = resolutionIndex == 1 ? fullResStorage_ : lowResStorages_.get(resolutionIndex - 1);
         Set<String> imageKeys = previousLevelStorage.imageKeys();
         for (String key : imageKeys) {
            HashMap<String, Object> axes = IndexEntryData.deserializeAxes(key);
            int previousResCol = (Integer) axes.get(COL_AXIS);
            int previousResRow = (Integer) axes.get(ROW_AXIS);

            TaggedImage ti = previousLevelStorage.getImage(key);
            int bitDepth = previousLevelStorage.getEssentialImageMetadata(key).bitDepth;
            boolean rgb = previousLevelStorage.getEssentialImageMetadata(key).rgb;
            addToLowResStorage(ti, axes,
                    resolutionIndex - 1, previousResRow, previousResCol, rgb, bitDepth);
         }
      }
   }


   /**
    * Increases the reosolutions in the pyramid.  Most often called by the UI if it
    * needs to zoom out further.
    *
    * @param newMaxResolutionLevel Next new resolution level.
    */
   @Override
   public void increaseMaxResolutionLevel(int newMaxResolutionLevel) {
      if (!tiled_) {
         return; // only tiled images support multiple resolutions
      }
      int oldMaxResolutionLevel = maxResolutionLevel_;
      // Clamp only the requested new level, and never reduce an already-higher maxResolutionLevel_
      int requestedMaxResolutionLevel = Math.min(newMaxResolutionLevel, MAX_RESOLUTION_LEVEL);
      maxResolutionLevel_ = Math.max(requestedMaxResolutionLevel, oldMaxResolutionLevel);
      if (fullResStorage_.imageKeys().size() == 0) {
         //nothing to do because data not yet arrived
         return;
      }

      for (int i = oldMaxResolutionLevel + 1; i <= maxResolutionLevel_; i++) {
         //add any new one this requires
         final int level = i;
         blockingWritingTaskHandoff(() -> {
            populateNewResolutionLevel(level, true);
            return null;
         });
      }
   }

   /**
    * Adds the specified image to all lower resolution storages.
    * The number of lower resolution storages is given by the variable maxResolutionLevel_.
    * If the lower resolution image already exists, the given image will be added as a
    * tile at the correct location.
    *
    * @param img The image to add
    * @param axes The axes of the image
    * @param originalResIndex The resolution index of the image
    * @param originalLevelRow The row of the image at the input resolution
    * @param originalLevelCol The column of the image at the input resolution
    * @param rgb Whether the image is rgb
    * @param bitDepth The bit depth of the image
    */
   private void addToLowResStorage(TaggedImage img, HashMap<String, Object> axes,
                                     int originalResIndex, int originalLevelRow, int originalLevelCol,
                                     boolean rgb, int bitDepth) {
      //Read indices
      Object previousLevelPix = img.pix;
      int resolutionIndex = originalResIndex + 1;

      int row = originalLevelRow;
      int col = originalLevelCol;

      while (resolutionIndex <= maxResolutionLevel_) {
         //Create this storage level if needed and add all existing tiles form the previous one
         if (!lowResStorages_.containsKey(resolutionIndex)) {
            //re-add all tiles from previous res level
            populateNewResolutionLevel(resolutionIndex, false);
         }

         //copy and change row and col to reflect lower resolution
         HashMap<String, Object> axesCopy = IndexEntryData.deserializeAxes(IndexEntryData.serializeAxes(axes));
         axesCopy.put(COL_AXIS, Math.floorDiv(col, 2));
         axesCopy.put(ROW_AXIS, Math.floorDiv(row, 2));

         if (lowResStorages_.get(resolutionIndex) == null) {
            System.out.println("null storage at res index: " + resolutionIndex);
         }

         //Create pixels or get appropriate pixels to add to
         TaggedImage existingImage = lowResStorages_.get(resolutionIndex).getImage(IndexEntryData.serializeAxes(axesCopy));

         Object currentLevelPix;
         if (existingImage == null) {
            if (rgb) {
               currentLevelPix = new byte[tileWidth_ * tileHeight_ * 4];
            } else if (img.pix instanceof byte[]) {
               currentLevelPix = new byte[tileWidth_ * tileHeight_];
            } else {
               currentLevelPix = new short[tileWidth_ * tileHeight_];
            }
         } else {
            currentLevelPix = existingImage.pix;
         }

         downsample(currentLevelPix, previousLevelPix, row, col, resolutionIndex, rgb);

         // store this tile in the storage class corresponding to this resolution
         try {
            String indexKey = IndexEntryData.serializeAxes(axesCopy);
            if (existingImage == null) {     //Image doesn't yet exist at this level, so add it
               // create a copy of tags so tags from a different res level are not inadvertently modified
               // while waiting for being written to disk
               JSONObject tags = new JSONObject(img.tags.toString());
               // modify tags to reflect image size, and correct position index
               lowResStorages_.get(resolutionIndex).putImage(
                       indexKey, currentLevelPix, tags.toString().getBytes(),
                       rgb, tileHeight_, tileWidth_, bitDepth);
            } else {
               lowResStorages_.get(resolutionIndex).overwritePixels(indexKey, currentLevelPix, rgb);
            }

         } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Could not modify tags for lower resolution level");
         }

         // go on to next level of downsampling
         previousLevelPix = currentLevelPix;
         resolutionIndex++;
         row = Math.floorDiv(row, 2);
         col = Math.floorDiv(col, 2);
      }
   }

   private void createDownsampledStorage(int resIndex) {
      String dsDir = directory_ + (directory_.endsWith(File.separator) ? "" : File.separator)
              + DOWNSAMPLE_SUFFIX + (1 << resIndex);
      try {
         createDir(dsDir);
      } catch (Exception ex) {
         throw new RuntimeException("copuldnt create directory");
      }
      try {
         JSONObject smd = new JSONObject(summaryMD_.toString());
         ResolutionLevel storage = new ResolutionLevel(dsDir, true, smd, this, prefix_);
         lowResStorages_.put(resIndex, storage);
      } catch (Exception ex) {
         throw new RuntimeException("Couldnt create downsampled storage");
      }
   }

   /**
    * Throws an exception if there was an error writing to disk.
    */
   public void checkForWritingException() throws Exception {
      if (writingException_ != null) {
         throw new Exception(writingException_);
      }
   }

   /**
    * This version works for regular, non-multiresolution data.
    *
    */
   public Future<IndexEntryData> putImage(Object pixels, JSONObject metadata,
                                          HashMap<String, Object> axessss, boolean rgb,
                                          int bitDepth, int imageHeight, int imageWidth) {
      try {
         checkForWritingException();
      } catch (Exception e) {
         throw new RuntimeException(e);
      }
      final TaggedImage ti = new TaggedImage(pixels, metadata);

      // Make sure each axis takes all integer or all string values
      for (String axisName : axessss.keySet()) {
         if (!axisTypes_.containsKey(axisName)) {
            axisTypes_.put(axisName, axessss.get(axisName).getClass());
         }
         if (!axessss.get(axisName).getClass().equals(axisTypes_.get(axisName))) {
            throw new RuntimeException("can't mix String and Integer values along an axis");
         }
      }

      if (!firstImageAdded_) {
         firstImageAdded_ = true;
         fullResTileWidthIncludingOverlap_ = imageWidth;
         fullResTileHeightIncludingOverlap_ = imageHeight;
         tileWidth_ = fullResTileWidthIncludingOverlap_ - xOverlap_;
         tileHeight_ = fullResTileHeightIncludingOverlap_ - yOverlap_;
      }


      if (debugLogger_ != null) {
         debugLogger_.accept(
                 "Adding image " + getAxesString(axessss)
                         + "\nwriting_queue_size= " + writingTaskQueue_.size());
      }
      // serialize metadata before adding to writing thread to speed performance
      byte[] metadataBytes = metadata.toString().getBytes(StandardCharsets.UTF_8);
      String indexKey = IndexEntryData.serializeAxes(axessss);
      fullResStorage_.addToWritePendingImages(indexKey, ti,
              new EssentialImageMetadata(imageWidth, imageHeight, bitDepth, rgb));

      //Submit writing task on a dedicated thread
      return blockingWritingTaskHandoff(new Callable<IndexEntryData>() {
         @Override
         public IndexEntryData call() {
            try {
               //Make a local copy
               HashMap<String, Object> axes = new HashMap<>(axessss);
               imageAxes_.add(axes);

               if (debugLogger_ != null) {
                  debugLogger_.accept("putting image in storage");
               }
               //write to full res storage as normal (i.e. with overlap pixels present)
               IndexEntryData ied = fullResStorage_.putImage(indexKey, pixels, metadataBytes,
                       rgb, imageHeight, imageWidth, bitDepth);
               return ied;
            } catch (Exception ex) {
               writingException_ = ex;
               return null;
            }
         }
      });
   }

   static String getAxesString(HashMap<String, Object> axes) {
      StringBuilder s = new StringBuilder();
      for (String key : axes.keySet()) {
         s.append(key).append("  ").append(axes.get(key)).append(",  ");
      }
      return s.toString();
   }

   /**
    * This version is called by programs doing dynamic stitching (i.e.
    * micro-magellan). Axes must contain "position" mapping to a desired position index
    *
    * @return
    */
   @Override
   public Future<IndexEntryData> putImageMultiRes(Object pixels, JSONObject metadata, final HashMap<String,
           Object> axes, boolean rgb, int bitDepth, int imageHeight, int imageWidth) {
      try {
         checkForWritingException();
      } catch (Exception e) {
         throw new RuntimeException(e);
      }
      TaggedImage ti = new TaggedImage(pixels, metadata);
      if (!firstImageAdded_) {
         // Technically this doesn't need to be parsed here, because it should be fixed
         // for the whole dataset, NOT interpretted at runtime, but whatever
         firstImageAdded_ = true;
         fullResTileWidthIncludingOverlap_ = imageWidth;
         fullResTileHeightIncludingOverlap_ = imageHeight;
         tileWidth_ = fullResTileWidthIncludingOverlap_ - xOverlap_;
         tileHeight_ = fullResTileHeightIncludingOverlap_ - yOverlap_;
      }

      byte[] metadataBytes = metadata.toString().getBytes();
      String indexKey = IndexEntryData.serializeAxes(StorageMD.getAxes(ti.tags));
      fullResStorage_.addToWritePendingImages(indexKey, ti,
              new EssentialImageMetadata(imageWidth, imageHeight, bitDepth, rgb));
      return blockingWritingTaskHandoff(() -> {
         IndexEntryData ied;
         try {
            if (tiled_) {
               if (!axes.containsKey(ROW_AXIS) || !axes.containsKey(COL_AXIS)) {
                  throw new RuntimeException("axes must contain row and column infor");
               }
            }
            imageAxes_.add(axes);

            //write to full res storage as normal (i.e. with overlap pixels present)
            ied = fullResStorage_.putImage(
                    indexKey, pixels, metadataBytes, rgb, imageHeight, imageWidth, bitDepth);

            if (tiled_) {
               //check if maximum resolution level needs to be updated based on full size of image
               int row = (Integer) axes.get(ROW_AXIS);
               int col = (Integer) axes.get(COL_AXIS);
               // addResolutionsUpTo(maxResIndex);
               addToLowResStorage(ti, axes, 0, row, col, rgb, bitDepth);
            }

         } catch (IOException ex) {
            throw new RuntimeException(ex.toString());
         }
         return ied;
      });
   }

   public boolean hasImage(HashMap<String, Object> axes, int downsampleIndex) {
      if (downsampleIndex == 0) {
         return fullResStorage_.hasImage(IndexEntryData.serializeAxes(axes));
      } else {
         return lowResStorages_.containsKey(downsampleIndex) && lowResStorages_.get(downsampleIndex)
                 .hasImage(IndexEntryData.serializeAxes(axes));
      }
   }

   @Override
   public TaggedImage getImage(HashMap<String, Object> axes) {
      //full resolution
      return getImage(axes, 0);
   }

   @Override
   public JSONObject getImageMetadata(HashMap<String, Object> axes) {
      if (fullResStorage_ == null) {
         return null;
      }
      return fullResStorage_.getImageTags(IndexEntryData.serializeAxes(axes));
   }

   @Override
   public TaggedImage getSubImage(HashMap<String, Object> axes, int xOffset, int yOffset, int width,
                                  int height) {
      return getDisplayImage(axes, 0, xOffset, yOffset, width, height);
   }

   @Override
   public EssentialImageMetadata getEssentialImageMetadata(HashMap<String, Object> axes,
                                                           int downsampleIndex) {
      if (downsampleIndex == 0) {
         return fullResStorage_.getEssentialImageMetadata(IndexEntryData.serializeAxes(axes));
      } else {
         return lowResStorages_.get(downsampleIndex).getEssentialImageMetadata(IndexEntryData.serializeAxes(axes));
      }
   }

   @Override
   public EssentialImageMetadata getEssentialImageMetadata(HashMap<String, Object> axes) {
      if (tiled_) {
         // essential metadata should be the same across all rows and cols so just find some math here
         for (HashMap<String, Object> storedAxes : getAxesSet()) {
            boolean match = true;
            for (String axis : axes.keySet()) {
               if (!axes.get(axis).equals(storedAxes.get(axis))) {
                  match = false;
               }
               if (match) {
                  return fullResStorage_.getEssentialImageMetadata(IndexEntryData.serializeAxes(storedAxes));
               }
            }
         }
         throw new RuntimeException("No match found"); // This shouldn't happen
      } else {
         return fullResStorage_.getEssentialImageMetadata(IndexEntryData.serializeAxes(axes));
      }
   }

   @Override
   public boolean hasImage(HashMap<String, Object> axes) {
      return hasImage(axes, 0);
   }

   @Override
   public TaggedImage getImage(HashMap<String, Object> axes, int dsIndex) {
      //return a single tile from the full res image
      if (fullResStorage_ == null || (tiled_ && lowResStorages_ == null)
              || (tiled_ && !lowResStorages_.containsKey(dsIndex) && dsIndex != 0)) {
         return null;
      }
      if (dsIndex == 0) {
         return fullResStorage_.getImage(IndexEntryData.serializeAxes(axes));
      } else {
         return lowResStorages_.get(dsIndex).getImage(IndexEntryData.serializeAxes(axes));
      }
   }

   private Future<IndexEntryData> blockingWritingTaskHandoff(Callable<IndexEntryData> r) {
      //Wait if queue is full, otherwise add and signal to running executor do it
      try {
         Future<IndexEntryData> f = writingExecutor_.submit(new Callable<IndexEntryData>() {
            @Override
            public IndexEntryData call() {
               try {
                  return writingTaskQueue_.take().call();
               } catch (Exception e) {
                  throw new RuntimeException(e);
               }
            }
         });
         writingTaskQueue_.put(r);
         return f;
      } catch (InterruptedException e) {
         throw new RuntimeException(e);
      }
   }

   /**
    * Signal to finish writing and block until everything pending is done.
    */
   public void finishedWriting()  {
      if (loaded_ && writingExecutor_ == null) {
         return;
      }
      if (debugLogger_ != null) {
         debugLogger_.accept("Finished writing. Remaining writing task queue size = " + writingTaskQueue_.size());
      }
      blockingWritingTaskHandoff(new Callable<IndexEntryData>() {
         @Override
         public IndexEntryData call() {
            if (debugLogger_ != null) {
               debugLogger_.accept("Finishing writing executor");
            }
            if (finished_) {
               return null;
            }
            if (debugLogger_ != null) {
               debugLogger_.accept("Finishing fullres storage");
            }
            fullResStorage_.finished();
            if (tiled_) {
               for (ResolutionLevel s : lowResStorages_.values()) {
                  if (s != null) {
                     //s shouldn't be null ever, this check is to prevent window from getting into unclosable state
                     //when other bugs prevent storage from being properly created
                     s.finished();
                  }
               }
            }
            if (debugLogger_ != null) {
               debugLogger_.accept("Shutting down writing excutor");
            }
            writingExecutor_.shutdown();
            if (displaySettings_ != null) {
               DisplaySettingsWriter w = new DisplaySettingsWriter(directory_);
               try {
                  w.add(displaySettings_);
               } catch (IOException e) {
                  e.printStackTrace();
               }
               w.finishedWriting();
            }
            if (debugLogger_ != null) {
               debugLogger_.accept("Display settings written");
            }
            return null;
         }
      });
      if (debugLogger_ != null) {
         debugLogger_.accept("Awaiting writing executor termination");
      }
      while (true) {
         try {
            if (writingExecutor_.awaitTermination(10, TimeUnit.MILLISECONDS)) {
               break;
            }
         } catch (InterruptedException e) {
            finished_ = true;
            throw new RuntimeException(e);
         }
      }
      finished_ = true;
      if (debugLogger_ != null) {
         debugLogger_.accept("Writing executor complete");
      }
   }

   @Override
   public void addImageWrittenListener(ImageWrittenListener iwc) {
      //deprecated
   }

   public boolean isFinished() {
      return finished_;
   }

   public JSONObject getSummaryMetadata() {
      return fullResStorage_.getSummaryMetadata();
   }

   public JSONObject getDisplaySettings() {
      return displaySettings_;
   }

   public void closeAndWait() throws InterruptedException {
      doClose();
   }

   public void close() {
      //run close on a new thread
      new Thread(new Runnable() {
         @Override
         public void run() {
            doClose();
         }
      }).start();
   }

   private void doClose() {
      //put closing on differnt channel so as to not hang up EDT while waiting for finishing
      //but cant put on writing executor because thats shutdown
      if (writingExecutor_ != null) {
         if (!writingExecutor_.isShutdown()) {
            // finishedWriting() was not called; initiate shutdown now so awaitTermination returns
            writingExecutor_.shutdown();
         }
         while (true) {
            try {
               if (writingExecutor_.awaitTermination(10, TimeUnit.MILLISECONDS)) {
                  break;
               }
            } catch (InterruptedException e) {
               throw new RuntimeException(e);
            }
         }
      }
      fullResStorage_.close();
      for (ResolutionLevel s : lowResStorages_.values()) {
         if (s != null) { //this only happens if the viewer requested new resolution levels that were never filled in because no iamges arrived
            s.close();
         }
      }
   }

   public String getDiskLocation() {
      //For display purposes
      return directory_;
   }

   public long getDataSetSize() {
      long sum = 0;
      sum += fullResStorage_.getDataSetSize();
      for (ResolutionLevel s : lowResStorages_.values()) {
         sum += s.getDataSetSize();
      }
      return sum;
   }

   //Copied from MMAcquisition
   private String getUniqueAcqDirName(String root, String prefix) throws Exception {
      File rootDir = createDir(root);
      int curIndex = getCurrentMaxDirIndex(rootDir, prefix + "_");
      return prefix + "_" + (1 + curIndex);
   }

   private static int getCurrentMaxDirIndex(File rootDir, String prefix) throws NumberFormatException {
      int maxNumber = 0;
      if (rootDir == null) {
         return maxNumber;
      }
      int number;
      String theName;
      for (File acqDir : rootDir.listFiles()) {
         theName = acqDir.getName();
         if (theName.toUpperCase().startsWith(prefix.toUpperCase())) {
            try {
               //e.g.: "blah_32.ome.tiff"
               Pattern p = Pattern.compile("\\Q" + prefix.toUpperCase() + "\\E" + "(\\d+).*+");
               Matcher m = p.matcher(theName.toUpperCase());
               if (m.matches()) {
                  number = Integer.parseInt(m.group(1));
                  if (number >= maxNumber) {
                     maxNumber = number;
                  }
               }
            } catch (NumberFormatException e) {
            } // Do nothing.
         }
      }
      return maxNumber;
   }

   /**
    *
    * @return set of points (col, row) with indices of tiles that have been
    * added at this slice index
    */
   public Set<Point> getTileIndicesWithDataAt(String name, int sliceIndex) {
      Set<Point> exploredTiles = new TreeSet<>((o1, o2) -> {
         if (o1.x != o2.x) {
            return o1.x - o2.x;
         } else if (o1.y != o2.y) {
            return o1.y - o2.y;
         }
         return 0;
      });
      for (HashMap<String, Object> s : imageAxes_) {
         if ((Integer) s.get(name) == sliceIndex) {
            exploredTiles.add(new Point((Integer) s.get(COL_AXIS), (Integer) s.get(ROW_AXIS)));
         }

      }
      return exploredTiles;
   }

   @Override
   public Set<Point> getTileIndicesWithDataAt(int zIndex) {
      throw new RuntimeException("Call the non deprecated version of this method instead");
   }

   private long getMinRow() {
      if (imageAxes_.isEmpty()) {
         return 0;
      }
      return imageAxes_.stream().mapToInt(value -> (Integer) value.get(ROW_AXIS)).min().getAsInt();
   }

   private long getMinCol() {
      if (imageAxes_.isEmpty()) {
         return 0;
      }
      return imageAxes_.stream().mapToInt(value -> (Integer) value.get(COL_AXIS)).min().getAsInt();
   }

   @Override
   public Set<HashMap<String, Object>> getAxesSet() {
      return imageAxes_;
   }


   //
   // Buffer allocation and recycling
   //

   // The idea here is to recycle the direct buffers for image pixels, because
   // allocation is slow. We do not need a large pool,
   // because the only aim is to avoid situations where allocation is limiting
   // at steady state. If writing is, on average, faster than incoming images,
   // the pool should always have a buffer ready for a new request.
   // Ideally we would also evict unused buffers after a timeout, so as not to
   // leak memory after writing has concluded.


   private static Buffer allocateByteBuffer(int capacity) {
      return ByteBuffer.allocateDirect(capacity).order(BYTE_ORDER);
   }

   Buffer getSmallBuffer(int capacity) {
      return allocateByteBuffer(capacity);
   }

   Buffer getLargeBuffer(int capacity) {
      if (capacity < BUFFER_RECYCLE_SIZE_MIN) {
         return allocateByteBuffer(capacity);
      }
      if (BUFFER_POOL_SIZE == 0) {
         return allocateByteBuffer(capacity);
      }

      if (!pooledBuffers_.containsKey(capacity)) {
         pooledBuffers_.put(capacity, new ArrayDeque<>(BUFFER_POOL_SIZE));
      }

      // Recycle in LIFO order (smaller images may still be in L3 cache)
      ByteBuffer b = pooledBuffers_.get(capacity).pollFirst();

      if (b != null) {
         // Ensure correct byte order in case recycled from other source
         b.order(BYTE_ORDER);
         //You can't chain the previous and following calls together or you get a weird java error
         b.clear();
         return b;
      }
      return allocateByteBuffer(capacity);
   }

   void tryRecycleLargeBuffer(ByteBuffer b) {
      // Keep up to BUFFER_POOL_SIZE direct buffers of the current size
      if (BUFFER_POOL_SIZE == 0 || !b.isDirect()) {
         return;
      }
      if (!pooledBuffers_.containsKey(b.capacity())) {
         pooledBuffers_.put(b.capacity(), new ArrayDeque<>(BUFFER_POOL_SIZE));
      }

      if (pooledBuffers_.get(b.capacity()).size() == BUFFER_POOL_SIZE) {
         pooledBuffers_.get(b.capacity()).removeLast(); // Discard oldest
      }
      pooledBuffers_.get(b.capacity()).addFirst(b);
   }

}
