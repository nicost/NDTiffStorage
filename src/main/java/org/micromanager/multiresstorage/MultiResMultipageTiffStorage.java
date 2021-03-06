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
package org.micromanager.multiresstorage;

import java.awt.Point;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import mmcorej.TaggedImage;
import mmcorej.org.json.JSONArray;
import mmcorej.org.json.JSONException;
import mmcorej.org.json.JSONObject;

/**
 * This class manages multiple multipage Tiff datasets, averaging multiple 2x2
 * squares of pixels to create successively lower resolutions until the
 * downsample factor is greater or equal to the number of tiles in a given
 * direction. This condition ensures that pixels will always be divisible by the
 * downsample factor without truncation
 *
 */
public class MultiResMultipageTiffStorage implements StorageAPI {

   public static final String TIME_AXIS = "time";
   public static final String CHANNEL_AXIS = "channel";
   public static final String Z_AXIS = "z";
   public static final String POSITION_AXIS = "position";

   private static final String FULL_RES_SUFFIX = "Full resolution";
   private static final String DOWNSAMPLE_SUFFIX = "Downsampled_x";
   private ResolutionLevel fullResStorage_;
   private TreeMap<Integer, ResolutionLevel> lowResStorages_; //map of resolution index to storage instance
   private String directory_;
   private JSONObject summaryMD_, displaySettings_;
   private int xOverlap_, yOverlap_;
   private int fullResTileWidthIncludingOverlap_, fullResTileHeightIncludingOverlap_;
   private int tileWidth_, tileHeight_; //Indpendent of zoom level because tile sizes stay the same--which means overlap is cut off
   private PositionManager posManager_;
   private volatile boolean finished_;
   private String uniqueAcqName_;
   private int byteDepth_;
   private boolean rgb_;
   private ThreadPoolExecutor writingExecutor_;
   private volatile int maxResolutionLevel_ = 0;
   private boolean loaded_, tiled_;
   private ConcurrentHashMap<String, Integer> superChannelNames_ = new ConcurrentHashMap<String, Integer>();
   private CopyOnWriteArrayList<String> positions_ = new CopyOnWriteArrayList<String>();
   private Set<HashMap<String, Integer>> imageAxes_ = new HashSet<HashMap<String, Integer>>();

   private String prefix_;

   /**
    * Constructor to load existing storage from disk dir --top level saving
    * directory
    */
   public MultiResMultipageTiffStorage(String dir) throws IOException {
      loaded_ = true;
      directory_ = dir;
      finished_ = true;
      String fullResDir = dir + (dir.endsWith(File.separator) ? "" : File.separator) + FULL_RES_SUFFIX;
      //create fullResStorage
      fullResStorage_ = new ResolutionLevel(fullResDir, false, null, null, this, -1, -1, false, -1);
      summaryMD_ = fullResStorage_.getSummaryMetadata();
      try {
         tiled_ = StorageMD.getTiledStorage(summaryMD_);
      } catch (Exception e) {
         tiled_ = true; //Backwards compat
      }

      //reconstruct map of super channel names to channel indices, and set
      //of all image axes
      for (String s : fullResStorage_.imageKeys()) {
         HashMap<String, Integer> map = new HashMap<String, Integer>();
         String[] indices = s.split("_");
         int cIndex = Integer.parseInt(indices[0]);
         int zIndex = Integer.parseInt(indices[1]);
         int tIndex = Integer.parseInt(indices[2]);
         int pIndex = Integer.parseInt(indices[3]);
         if (!superChannelNames_.values().contains(cIndex)) {
            String channelName = StorageMD.getChannelName(fullResStorage_.getImageTags(cIndex, zIndex, tIndex, pIndex));
            superChannelNames_.put(channelName, cIndex);
         }
         String channelName = null;
         for (String name : superChannelNames_.keySet()) {
            channelName = name;
            if (superChannelNames_.get(name) == cIndex) {
               break;
            }
         }
         //This code adds in c index, as well as any others
         String[] otherAxes = channelName.split("Axis_");
         for (String newax : otherAxes) {
            if (newax.isEmpty()) {
               continue;
            }
            map.put(newax.split("_")[0], Integer.parseInt(newax.split("_")[1]));
         }

         //TODO: could remove these if they dont have values other than 0,
         //but fine to leave them for time being cause viewer will ignore
         map.put(TIME_AXIS, tIndex);
         map.put(Z_AXIS, zIndex);
         map.put(POSITION_AXIS, pIndex);
         imageAxes_.add(map);
      }

      //iterate 
      rgb_ = false;
      byteDepth_ = fullResStorage_.getByteDepth();
      fullResTileWidthIncludingOverlap_ = fullResStorage_.getWidth();
      fullResTileHeightIncludingOverlap_ = fullResStorage_.getHeight();

      xOverlap_ = StorageMD.getPixelOverlapX(summaryMD_);
      yOverlap_ = StorageMD.getPixelOverlapY(summaryMD_);

      tileWidth_ = fullResTileWidthIncludingOverlap_ - xOverlap_;
      tileHeight_ = fullResTileHeightIncludingOverlap_ - yOverlap_;

      lowResStorages_ = new TreeMap<Integer, ResolutionLevel>();
      //create low res storages
      int resIndex = 1;
      while (true) {
         String dsDir = directory_ + (directory_.endsWith(File.separator) ? "" : File.separator)
                 + DOWNSAMPLE_SUFFIX + (int) Math.pow(2, resIndex);
         if (!new File(dsDir).exists()) {
            break;
         }
         maxResolutionLevel_ = resIndex;
         lowResStorages_.put(resIndex, new ResolutionLevel(dsDir, false, null, null, this, -1, -1, false, -1));
         resIndex++;
      }

      //create position manager
      try {
         TreeMap<Integer, JSONObject> positions = new TreeMap<Integer, JSONObject>();
         for (String key : fullResStorage_.imageKeys()) {
            // array with entires channelIndex, sliceIndex, frameIndex, positionIndex
            int[] indices = StorageMD.getIndices(key);
            int posIndex = indices[3];
            if (!positions.containsKey(posIndex)) {
               //read rowIndex, colIndex, stageX, stageY from per image metadata
               JSONObject md = fullResStorage_.getImageTags(indices[0], indices[1], indices[2], indices[3]);
               try {
                  JSONObject pos = new JSONObject();
                  pos.put("GridColumnIndex", StorageMD.getGridCol(md));
                  pos.put("GridRowIndex", StorageMD.getGridRow(md));
                  pos.put("Properties", new JSONObject());
                  positions.put(posIndex, pos);
               } catch (Exception e) {
                  throw new RuntimeException("Couldn't create XY position JSONOBject");
               }
            }
         }
         JSONArray pList = new JSONArray();
         for (JSONObject xyPos : positions.values()) {
            pList.put(xyPos);
         }
         if (tiled_) {
            posManager_ = new PositionManager(pList, lowResStorages_.size());
         }

      } catch (Exception e) {
         throw new RuntimeException("Couldn't create position manager");
      }
   }

   /**
    * Construcotr for new storage that doesn't parse summary metadata
    */
   public MultiResMultipageTiffStorage(String dir, String name, JSONObject summaryMetadata,
           int overlapX, int overlapY, int width, int height, int byteDepth, boolean tiled) {
      tiled_ = tiled;
      xOverlap_ = overlapX;
      yOverlap_ = overlapY;
      byteDepth_ = byteDepth;
      fullResTileWidthIncludingOverlap_ = width;
      fullResTileHeightIncludingOverlap_ = height;
      tileWidth_ = fullResTileWidthIncludingOverlap_ - xOverlap_;
      tileHeight_ = fullResTileHeightIncludingOverlap_ - yOverlap_;
      prefix_ = name;

      loaded_ = false;
      writingExecutor_ = new ThreadPoolExecutor(1, 1, 0, TimeUnit.NANOSECONDS,
              new LinkedBlockingQueue<java.lang.Runnable>());
      try {
         //make a copy in case tag changes are needed later
         summaryMD_ = new JSONObject(summaryMetadata.toString());
         StorageMD.setPixelOverlapX(summaryMD_, xOverlap_);
         StorageMD.setPixelOverlapY(summaryMD_, yOverlap_);
         StorageMD.setTiledStorage(summaryMD_, tiled_);
      } catch (JSONException ex) {
         throw new RuntimeException("Couldnt copy summary metadata");
      }

      //prefix is provided by summary metadata
      try {
         uniqueAcqName_ = getUniqueAcqDirName(dir, name);
         //create acqusition directory for actual data
         directory_ = dir + (dir.endsWith(File.separator) ? "" : File.separator) + uniqueAcqName_;
      } catch (Exception e) {
         throw new RuntimeException("Couldn't make acquisition directory");
      }

      //create directory for full res data
      String fullResDir = directory_ + (dir.endsWith(File.separator) ? "" : File.separator) + FULL_RES_SUFFIX;
      try {
         createDir(fullResDir);
      } catch (Exception ex) {
         throw new RuntimeException("couldn't create saving directory");
      }

      if (tiled_) {
         try {
            posManager_ = new PositionManager();
         } catch (Exception e) {
            throw new RuntimeException("Couldn't create position manaher");
         }
      }
      try {
         //Create full Res storage
         fullResStorage_ = new ResolutionLevel(fullResDir, true, summaryMetadata, writingExecutor_, this,
                 fullResTileWidthIncludingOverlap_, fullResTileHeightIncludingOverlap_,
                 rgb_, byteDepth_);
      } catch (IOException ex) {
         throw new RuntimeException("couldn't create Full res storage");
      }
      lowResStorages_ = new TreeMap<Integer, ResolutionLevel>();
   }

   static File createDir(String dir) {
      File dirrr = new File(dir);
      if (!dirrr.exists()) {
         if (!dirrr.mkdirs()) {
            throw new RuntimeException("Unable to create directory " + dir);
         }
      }
      return dirrr;
   }

   public void setDisplaySettings(JSONObject displaySettings) {
      try {
         if (displaySettings != null) {
            displaySettings_ = new JSONObject(displaySettings.toString());
            if (!loaded_) {
               fullResStorage_.setDisplaySettings();
            }
         }
      } catch (JSONException ex) {
         throw new RuntimeException();
      }
   }

//   public static JSONObject readSummaryMetadata(String dir) throws IOException {
//      String fullResDir = dir + (dir.endsWith(File.separator) ? "" : File.separator) + FULL_RES_SUFFIX;
//      return TaggedImageStorageMultipageTiff.readSummaryMD(fullResDir);
//   }
   public String getUniqueAcqName() {
      return uniqueAcqName_ + ""; //make new instance
   }

   public int getNumResLevels() {
      return maxResolutionLevel_ + 1;
   }

   public int[] getImageBounds() {
      if (!tiled_) {
         return new int[]{0, 0, tileWidth_, tileHeight_};
      }
      if (!loaded_) {
         return new int[]{0, 0, getNumCols() * tileWidth_, getNumRows() * tileHeight_};
      } else {
         int yMin = (int) (getMinRow() * tileHeight_);
         int xMin = (int) (getMinCol() * tileWidth_);
         int xMax = (int) (getNumCols() * tileWidth_ + xMin);
         int yMax = (int) (getNumRows() * tileHeight_ + yMin);
         return new int[]{xMin, yMin, xMax, yMax};
      }
   }

   private int getNumRows() {
      return posManager_.getNumRows();
   }

   private int getNumCols() {
      return posManager_.getNumCols();
   }

   /*
    * It doesnt matter what resolution level the pixel is at since tiles
    * are the same size at every level
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
    * Read tile, and try deleting and try deleting slice/frame/pos indices to
    * find correct tile This is used in the case that certain axes aren't
    * present for certain images, so we want them to be shown for all values of
    * the missing axis
    *
    * @param dsIndex
    * @param channel
    * @param slice
    * @param frame
    * @param posIndex
    * @return
    */
   private TaggedImage readImageWithMissingAxes(int dsIndex, int channel, 
           Integer slice, Integer frame, int posIndex) {
      ResolutionLevel storage;
      if (dsIndex == 0) {
         storage = fullResStorage_;
      } else {
         if (lowResStorages_.get(dsIndex) == null) {
            return null;
         }
         storage = lowResStorages_.get(dsIndex);
      }

      return storage.getImage(channel, 
              slice != null ? slice : 0, 
              frame != null ? frame : 0, 
              posIndex);
   }

   /**
    * Return a subimage of the larger stitched image at the appropriate zoom
    * level, loading only the tiles neccesary to form the subimage
    *
    * @param channel
    * @param slice
    * @param frame
    * @param dsIndex 0 for full res, 1 for 2x downsample, 2 for 4x downsample,
    * etc..
    * @param x coordinate of leftmost pixel in requested resolution
    * @param y coordinate of topmost pixel in requested resolution
    * @param width pixel width of image at requested resolution
    * @param height pixel height of image at requested resolution
    * @return Tagged image or taggeded image with background pixels and null
    * tags if no pixel data is present
    */
   public TaggedImage getStitchedImage(HashMap<String, Integer> axes,
           int dsIndex, int x, int y, int width, int height) {

      Integer frame = axes.containsKey(TIME_AXIS) ? axes.get(TIME_AXIS) : null;
      Integer slice = axes.containsKey(Z_AXIS) ? axes.get(Z_AXIS) : null;
      String superChannelName = getSuperChannelName(axes, false);
      int channel = superChannelNames_.get(superChannelName);

      Object pixels;
      if (rgb_) {
         pixels = new byte[width * height * 4];
      } else if (byteDepth_ == 1) {
         pixels = new byte[width * height];
      } else {
         pixels = new short[width * height];
      }
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
            TaggedImage tile = null;
            Integer posIndex;
            if (dsIndex == 0) {
               if (posManager_ == null) {
                  posIndex = axes.containsKey(POSITION_AXIS) ? axes.get(POSITION_AXIS) :
                          (tiled_ ? null : 0);
               } else {
                  posIndex = posManager_.getPositionIndexFromTilePosition(dsIndex, row, col);
               }
            } else {
               posIndex = posManager_.getPositionIndexFromTilePosition(dsIndex, row, col);
            }
            if (posIndex != null) {
               tile = readImageWithMissingAxes(dsIndex, channel, slice, frame, posIndex);
            }

            if (tile == null) {
               yOffset += lineHeights.get((int) (row - rowStart)); //increment y offset so new tiles appear in correct position
               continue; //If no data present for this tile go on to next one
            } else if ((tile.pix instanceof byte[] && ((byte[]) tile.pix).length == 0)
                    || (tile.pix instanceof short[] && ((short[]) tile.pix).length == 0)) {
               //Somtimes an inability to read IFDs soon after they are written results in an image being read 
               //with 0 length pixels. Can't figure out why this happens, but it is rare and will result at worst with
               //a black flickering during acquisition
               yOffset += lineHeights.get((int) (row - rowStart)); //increment y offset so new tiles appear in correct position
               continue;
            }
            //take top left tile for metadata
            if (topLeftMD == null) {
               topLeftMD = tile.tags;
            }
            //Copy pixels into the image to be returned
            //yOffset is how many rows from top of viewable area, y is top of image to top of area
            for (int line = yOffset; line < lineHeights.get((int) (row - rowStart)) + yOffset; line++) {
               int tileYPix = (int) ((y + line) % tileHeight_);
               int tileXPix = (int) ((x + xOffset) % tileWidth_);
               //make sure tile pixels are positive
               while (tileXPix < 0) {
                  tileXPix += tileWidth_;
               }
               while (tileYPix < 0) {
                  tileYPix += tileHeight_;
               }
               try {
                  int multiplier = rgb_ ? 4 : 1;
                  if (dsIndex == 0) {
                     //account for overlaps when viewing full resolution tiles
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

//   /**
//    * Called before any images have been added to initialize the resolution to
//    * the specifiec zoom level
//    *
//    * @param resIndex
//    */
//   public void initializeToLevel(int resIndex) {
//      //create a null pointer in lower res storages to signal addToLoResStorage function
//      //to continue downsampling to this level
//      maxResolutionLevel_ = resIndex;
//      //Make sure position nodes for lower resolutions are created if they weren't automatically
//      posManager_.updateLowerResolutionNodes(resIndex);
//   }
   /**
    * create an additional lower resolution levels for zooming purposes
    */
   private void addResolutionsUpTo(int index) throws InterruptedException, ExecutionException {
      if (index <= maxResolutionLevel_) {
         return;
      }
      int oldLevel = maxResolutionLevel_;
      maxResolutionLevel_ = index;
      //update position manager to reflect addition of new resolution level
      posManager_.updateLowerResolutionNodes(maxResolutionLevel_);
      ArrayList<Future> finished = new ArrayList<Future>();
      for (int i = oldLevel + 1; i <= maxResolutionLevel_; i++) {
         populateNewResolutionLevel(finished, i);
         for (Future f : finished) {
            f.get();
         }
      }
   }

   private void downsample(Object currentLevelPix, Object previousLevelPix, int fullResPositionIndex, int resolutionIndex) {
      //Determine which position in 2x2 this tile sits in
      int xPos = (int) Math.abs((posManager_.getGridCol(fullResPositionIndex, resolutionIndex - 1) % 2));
      int yPos = (int) Math.abs((posManager_.getGridRow(fullResPositionIndex, resolutionIndex - 1) % 2));
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
            int rgbMultiplier_ = rgb_ ? 4 : 1;
            for (int compIndex = 0; compIndex < (rgb_ ? 3 : 1); compIndex++) {
               int count = 1; //count is number of pixels (out of 4) used to create a pixel at this level
               //always take top left pixel, maybe take others depending on whether at image edge
               int sum = 0;
               if (byteDepth_ == 1 || rgb_) {
                  sum += ((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX) * rgbMultiplier_ + compIndex] & 0xff;
               } else {
                  sum += ((short[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX) * rgbMultiplier_ + compIndex] & 0xffff;
               }

               //pixel index can be different from index in tile at resolution level 0 if there is nonzero overlap
               if (x < previousLevelWidth - 1 && y < previousLevelHeight - 1) { //if not bottom right corner, add three more pix
                  count += 3;
                  if (byteDepth_ == 1 || rgb_) {
                     sum += (((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX + 1) * rgbMultiplier_ + compIndex] & 0xff)
                             + (((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1) * rgbMultiplier_ + compIndex] & 0xff)
                             + (((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) * rgbMultiplier_ + compIndex] & 0xff);
                  } else {
                     sum += (((short[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX + 1) * rgbMultiplier_ + compIndex] & 0xffff)
                             + (((short[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1) * rgbMultiplier_ + compIndex] & 0xffff)
                             + (((short[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) * rgbMultiplier_ + compIndex] & 0xffff);
                  }
               } else if (x < previousLevelWidth - 1) { //if not right edge, add one more pix
                  count++;
                  if (byteDepth_ == 1 || rgb_) {
                     sum += ((byte[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1) * rgbMultiplier_ + compIndex] & 0xff;
                  } else {
                     sum += ((short[]) previousLevelPix)[(pixelY * previousLevelWidth + pixelX + 1) * rgbMultiplier_ + compIndex] & 0xffff;
                  }
               } else if (y < previousLevelHeight - 1) { // if not bottom edge, add one more pix
                  count++;
                  if (byteDepth_ == 1 || rgb_) {
                     sum += ((byte[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) * rgbMultiplier_ + compIndex] & 0xff;
                  } else {
                     sum += ((short[]) previousLevelPix)[((pixelY + 1) * previousLevelWidth + pixelX) * rgbMultiplier_ + compIndex] & 0xffff;
                  }
               } else {
                  //it is the bottom right corner, no more pix to add
               }
               //add averaged pixel into appropriate quadrant of current res level
               //if full res tile has an odd number of pix, the last one gets chopped off
               //to make it fit into tile containers
               try {
                  int index = (((y + yPos * tileHeight_) / 2) * tileWidth_ + (x + xPos * tileWidth_) / 2) * rgbMultiplier_ + compIndex;
                  if (byteDepth_ == 1 || rgb_) {
                     ((byte[]) currentLevelPix)[index] = (byte) Math.round(sum / count);
                  } else {
                     ((short[]) currentLevelPix)[index] = (short) Math.round(sum / count);
                  }
               } catch (Exception e) {
                  throw new RuntimeException("Couldn't copy pixels to lower resolution");
               }

            }
         }
      }
   }

   private void populateNewResolutionLevel(List<Future> writeFinishedList, int resolutionIndex) {
      createDownsampledStorage(resolutionIndex);
      //add all tiles from existing resolution levels to this new one            
      ResolutionLevel previousLevelStorage
              = resolutionIndex == 1 ? fullResStorage_ : lowResStorages_.get(resolutionIndex - 1);
      Set<String> imageKeys = previousLevelStorage.imageKeys();
      for (String key : imageKeys) {
         String[] indices = key.split("_");
         TaggedImage ti = previousLevelStorage.getImage(Integer.parseInt(indices[0]), Integer.parseInt(indices[1]),
                 Integer.parseInt(indices[2]), Integer.parseInt(indices[3]));

         int channelIndex = Integer.parseInt(indices[0]);
         int zIndex = Integer.parseInt(indices[1]);
         int tIndex = Integer.parseInt(indices[2]);

         int fullResPosIndex = posManager_.getFullResPositionIndex(Integer.parseInt(indices[3]), resolutionIndex - 1);

         int rowIndex = (int) posManager_.getGridRow(fullResPosIndex, resolutionIndex);
         int colIndex = (int) posManager_.getGridCol(fullResPosIndex, resolutionIndex);
         writeFinishedList.addAll(addToLowResStorage(ti,
                 tIndex, zIndex, channelIndex, resolutionIndex - 1, fullResPosIndex,
                 rowIndex, colIndex));
      }
   }

   /**
    * return a future for when the current res level is done writing
    */
   private List<Future> addToLowResStorage(TaggedImage img, int tIndex, int zIndex,
           int channelIndex, int previousResIndex, int fullResPositionIndex, int rowIndex, int colIndex) {
      List<Future> writeFinishedList = new ArrayList<>();
      //Read indices

      Object previousLevelPix = img.pix;
      int resolutionIndex = previousResIndex + 1;

      while (resolutionIndex <= maxResolutionLevel_) {
         //Create this storage level if needed and add all existing tiles form the previous one
         if (!lowResStorages_.containsKey(resolutionIndex)) {
            //re add all tiles from previous res level
            populateNewResolutionLevel(writeFinishedList, resolutionIndex);
            //its been re added, so can return here and previous call will get to the code below
            return writeFinishedList;
         }

         //Create pixels or get appropriate pixels to add to
         TaggedImage existingImage = lowResStorages_.get(resolutionIndex).getImage(channelIndex, zIndex, tIndex,
                 posManager_.getLowResPositionIndex(fullResPositionIndex, resolutionIndex));
         Object currentLevelPix;
         if (existingImage == null) {
            if (rgb_) {
               currentLevelPix = new byte[tileWidth_ * tileHeight_ * 4];
            } else if (byteDepth_ == 1) {
               currentLevelPix = new byte[tileWidth_ * tileHeight_];
            } else {
               currentLevelPix = new short[tileWidth_ * tileHeight_];
            }
         } else {
            currentLevelPix = existingImage.pix;
         }

         downsample(currentLevelPix, previousLevelPix, fullResPositionIndex, resolutionIndex);

         //store this tile in the storage class correspondign to this resolution
         try {
            if (existingImage == null) {     //Image doesn't yet exist at this level, so add it
               //create a copy of tags so tags from a different res level arent inadverntanly modified
               // while waiting for being written to disk
               JSONObject tags = new JSONObject(img.tags.toString());
               //modify tags to reflect image size, and correct position index
//               MultiresMetadata.setWidth(tags, tileWidth_);
//               MultiresMetadata.setHeight(tags, tileHeight_);

               int positionIndex = posManager_.getLowResPositionIndex(fullResPositionIndex, resolutionIndex);
               Future f = lowResStorages_.get(resolutionIndex).putImage(new TaggedImage(currentLevelPix, tags),
                       prefix_, tIndex, channelIndex, zIndex, positionIndex);

               //need to make sure this one gets written before others can be overwritten
               f.get();
            } else {
               //Image already exists, only overwrite pixels to include new tiles
               writeFinishedList.addAll(lowResStorages_.get(resolutionIndex).overwritePixels(currentLevelPix,
                       channelIndex, zIndex, tIndex, posManager_.getLowResPositionIndex(fullResPositionIndex, resolutionIndex)));
            }
         } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("Couldnt modify tags for lower resolution level");
         }

         //go on to next level of downsampling
         previousLevelPix = currentLevelPix;
         resolutionIndex++;
      }
      return writeFinishedList;
   }

   private void createDownsampledStorage(int resIndex) {
      String dsDir = directory_ + (directory_.endsWith(File.separator) ? "" : File.separator)
              + DOWNSAMPLE_SUFFIX + (int) Math.pow(2, resIndex);
      try {
         createDir(dsDir);
      } catch (Exception ex) {
         throw new RuntimeException("copuldnt create directory");
      }
      try {
         JSONObject smd = new JSONObject(summaryMD_.toString());
//         //reset dimensions so that overlap not included
//         smd.put("Width", tileWidth_);
//         smd.put("Height", tileHeight_);
         ResolutionLevel storage = new ResolutionLevel(dsDir, true, smd, writingExecutor_, this,
                 tileWidth_, tileHeight_, false, byteDepth_);
         lowResStorages_.put(resIndex, storage);
      } catch (Exception ex) {
         throw new RuntimeException("Couldnt create downsampled storage");
      }
   }

   private String getSuperChannelName(HashMap<String, Integer> axes, boolean addNew) {
      HashMap<String, Integer> axesCopy = new HashMap<String, Integer>(axes);
      //the storage is specced for T C Z P, so remove PZT and combine
      //C with any other axes into a sueprchannel
      axesCopy.remove(POSITION_AXIS);
      axesCopy.remove(Z_AXIS);
      axesCopy.remove(TIME_AXIS);
      //if doesn't contain explicit channel index, default to 0
      if (!axesCopy.containsKey(CHANNEL_AXIS)) {
         axesCopy.put(CHANNEL_AXIS, 0);
      }

      //Convert all other remaining axes into a superchannel
      String superChannel = "";
      HashSet<String> sortedSet = new HashSet<String>(axesCopy.keySet());
      for (String s : sortedSet) {
         superChannel += "Axis_" + s + "_" + axesCopy.get(s);
      }
      //get index of superchannel

      if (!addNew) {
         if (superChannelNames_.contains(superChannel)) {
            return superChannel;
         }
         //If all the axes in the per channel match the one requested, but
         //there are also additional ones requested, count it as a match
         for (String scName : superChannelNames_.keySet()) {
            boolean matchesAll = true;
            for (String axis : axesCopy.keySet()) {
               if (scName.contains("Axis_" + axis) && 
                       !scName.contains("Axis_" + axis + "_" + axesCopy.get(axis))) {
                  matchesAll = false;
               }
            }
            if (matchesAll) {
               return scName;
            }
         } 
         System.err.println("Couldn't find super channel index");
       return null;
      } else {
         if (!superChannelNames_.keySet().contains(superChannel) && addNew) {
            int superChannelIndex = superChannelNames_.size();
            superChannelNames_.put(superChannel, superChannelIndex);
         }
         return superChannel;
      }
   }

   /**
    * This version works for regular, non-multiresolution data
    *
    * @param ti
    * @param axes
    */
   public void putImage(TaggedImage ti, HashMap<String, Integer> axes) {
      try {
         List<Future> writeFinishedList = new ArrayList<Future>();
         imageAxes_.add(axes);

         int pIndex = axes.containsKey(POSITION_AXIS) ? axes.get(POSITION_AXIS) : 0;
         int tIndex = axes.containsKey(TIME_AXIS) ? axes.get(TIME_AXIS) : 0;
         int zIndex = axes.containsKey(Z_AXIS) ? axes.get(Z_AXIS) : 0;
         //This call merges all other axes besides p z t into a superchannel,
         //Creating a new one if neccessary
         String superChannelName = getSuperChannelName(axes, true);
         //set the name because it will be needed in recovery

         StorageMD.setSuperChannelName(ti.tags, superChannelName);
         //make sure to put it in the metadata
         StorageMD.createAxes(ti.tags);
         for (String axis : axes.keySet()) {
            StorageMD.setAxisPosition(ti.tags, axis, axes.get(axis));
         }

         //write to full res storage as normal (i.e. with overlap pixels present)
         writeFinishedList.add(fullResStorage_.putImage(ti, prefix_,
                 tIndex, superChannelNames_.get(superChannelName), zIndex, pIndex));

//         //check if maximum resolution level needs to be updated based on full size of image
//         long fullResPixelWidth = getNumCols() * tileWidth_;
//         long fullResPixelHeight = getNumRows() * tileHeight_;
//         int maxResIndex = (int) Math.ceil(Math.log((Math.max(fullResPixelWidth, fullResPixelHeight)
//                 / 4)) / Math.log(2));
//
//         addResolutionsUpTo(maxResIndex);
//         writeFinishedList.addAll(addToLowResStorage(ti, tIndex, zIndex,
//                 superCIndex, 0, pIndex, row, col));
         for (Future f : writeFinishedList) {
            f.get();
         }
      } catch (IOException | ExecutionException | InterruptedException ex) {
         throw new RuntimeException(ex.toString());
      }
   }

   /**
    * This version is called by programs doing dynamic stitching (i.e.
    * micro-magellan). axes must contain "position" mapping to a desired position index
    *
    * Don't return until all images have been written to disk
    */
   public void putImage(TaggedImage ti, HashMap<String, Integer> axes, int row, int col) {
      try {

         List<Future> writeFinishedList = new ArrayList<Future>();

         if (tiled_) {
            if (!axes.containsKey(POSITION_AXIS)) {
               throw new RuntimeException("axes must contain a position index entry with \"position\" as key");
            }
         }
         int pIndex = axes.containsKey(POSITION_AXIS) ? axes.get(POSITION_AXIS) : 0;

         imageAxes_.add(axes);

         int tIndex = axes.containsKey(TIME_AXIS) ? axes.get(TIME_AXIS) : 0;
         int zIndex = axes.containsKey(Z_AXIS) ? axes.get(Z_AXIS) : 0;
         //This call merges all other axes besides p z t into a superchannel,
         //Creating a new one if neccessary
         String superChannelName = getSuperChannelName(axes, true);
         //set the name because it will be needed in recovery

         StorageMD.setSuperChannelName(ti.tags, superChannelName);
         //make sure to put it in the metadata
         StorageMD.createAxes(ti.tags);
         for (String axis : axes.keySet()) {
            StorageMD.setAxisPosition(ti.tags, axis, axes.get(axis));
         }

         //write to full res storage as normal (i.e. with overlap pixels present)
         writeFinishedList.add(fullResStorage_.putImage(ti, prefix_,
                 tIndex, superChannelNames_.get(superChannelName), zIndex, pIndex));

         if (tiled_) {
            //check if maximum resolution level needs to be updated based on full size of image
            long fullResPixelWidth = getNumCols() * tileWidth_;
            long fullResPixelHeight = getNumRows() * tileHeight_;
            int maxResIndex = (int) Math.ceil(Math.log((Math.max(fullResPixelWidth, fullResPixelHeight)
                    / 4)) / Math.log(2));

            //Make sure positon manager knows about potential new rows/cols
            posManager_.rowColReceived(row, col);
            addResolutionsUpTo(maxResIndex);
            writeFinishedList.addAll(addToLowResStorage(ti, tIndex, zIndex,
                    superChannelNames_.get(superChannelName), 0, pIndex, row, col));
         }

         for (Future f : writeFinishedList) {
            f.get();
         }
      } catch (IOException | ExecutionException | InterruptedException ex) {
         throw new RuntimeException(ex.toString());
      }
   }

   @Override
   public TaggedImage getImage(HashMap<String, Integer> axes) {
      //Convert axes to the 4 axes used by underlying storage by adding in
      //p z t as needed and converting c + remaining to superchannel
      axes = (HashMap<String, Integer>) axes.clone();
      int frame = axes.containsKey(TIME_AXIS) ? axes.get(TIME_AXIS) : 0;
      int slice = axes.containsKey(Z_AXIS) ? axes.get(Z_AXIS) : 0;
      int position = axes.containsKey(POSITION_AXIS) ? axes.get(POSITION_AXIS) : 0;
      int superChannel = superChannelNames_.get(getSuperChannelName(axes, false));
      //return a single tile from the full res image
      return fullResStorage_.getImage(superChannel, slice, frame, position);
   }

   public void finishedWriting() {
      if (finished_) {
         return;
      }
      fullResStorage_.finished();
      for (ResolutionLevel s : lowResStorages_.values()) {
         if (s != null) {
            //s shouldn't be null ever, this check is to prevent window from getting into unclosable state
            //when other bugs prevent storage from being properly created
            s.finished();
         }
      }
      writingExecutor_.shutdown();
      //shut down writing executor--pause here until all tasks have finished writing
      //so that no attempt is made to close the dataset (and thus the FileChannel)
      //before everything has finished writing
      //mkae sure all images have finished writing if they are on seperate thread 
      try {
         writingExecutor_.awaitTermination(5, TimeUnit.MILLISECONDS);
      } catch (InterruptedException ex) {
         throw new RuntimeException("unexpected interrup when closing image storage");
      }
      finished_ = true;
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

   public void close() {
      //put closing on differnt channel so as to not hang up EDT while waiting for finishing
      new Thread(new Runnable() {
         @Override
         public void run() {
            while (!finished_) {
               try {
                  Thread.sleep(5);
               } catch (InterruptedException ex) {
                  throw new RuntimeException("closing thread interrupted");
               }
            }
            fullResStorage_.close();
            for (ResolutionLevel s : lowResStorages_.values()) {
               if (s != null) { //this only happens if the viewer requested new resolution levels that were never filled in because no iamges arrived                  
                  s.close();
               }
            }
         }
      }, "closing thread").start();
   }

   public String getDiskLocation() {
      //For display purposes
      return directory_;
   }

   public int getNumChannels() {
      return fullResStorage_.getNumChannels();
   }

   public int getNumFrames() {
      return fullResStorage_.getMaxFrameIndexOpenedDataset() + 1;
   }

   public int getMinSliceIndexOpenedDataset() {
      return fullResStorage_.getMinSliceIndexOpenedDataset();
   }

   public int getMaxSliceIndexOpenedDataset() {
      return fullResStorage_.getMaxSliceIndexOpenedDataset();
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
   public Set<Point> getTileIndicesWithDataAt(int sliceIndex) {
      Set<Point> exploredTiles = new TreeSet<Point>(new Comparator<Point>() {
         @Override
         public int compare(Point o1, Point o2) {
            if (o1.x != o2.x) {
               return o1.x - o2.x;
            } else if (o1.y != o2.y) {
               return o1.y - o2.y;
            }
            return 0;
         }
      });
      for (HashMap<String, Integer> s : imageAxes_) {
         if (s.get("z") == sliceIndex) {
            exploredTiles.add(new Point((int) posManager_.getGridCol(s.get(POSITION_AXIS), 0),
                    (int) posManager_.getGridRow(s.get(POSITION_AXIS), 0)));
         }

      }
      return exploredTiles;
   }

   private long getMinRow() {
      return posManager_.getMinRow();
   }

   private long getMinCol() {
      return posManager_.getMinCol();
   }

   @Override
   public Set<HashMap<String, Integer>> getAxesSet() {
      return imageAxes_;
   }

}
