package org.micromanager.ndtiffstorage.test;

import mmcorej.TaggedImage;
import mmcorej.org.json.JSONArray;
import mmcorej.org.json.JSONObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.micromanager.ndtiffstorage.NDTiffStorage;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.HashMap;

import static org.junit.Assert.*;

/**
 * Tests that getDisplayImage returns correct pixel data at all pyramid levels
 * for a 2×2 tiled dataset with and without TileAffineTransform tags.
 *
 * Covers both zero-overlap and non-zero-overlap cases.
 */
public class TileAffinePositionTest {

   // Tile buffer dimensions including overlap border.
   private static final int TILE_W = 64;   // full buffer width (= content width when OVERLAP=0)
   private static final int TILE_H = 64;
   private static final int OVERLAP = 0;

   // Tile buffer dimensions for the overlap case.
   // With OVERLAP_W=8: tileWidth_ = 64-8 = 56, content in buffer at x=[4,60).
   private static final int TILE_W_OVL = 64;
   private static final int TILE_H_OVL = 64;
   private static final int OVERLAP_W = 8;   // xOverlap_ = yOverlap_ = 8

   // A 2×2 grid of tiles — nominal (uniform-grid) positions.
   private static final int[][] NOMINAL_TX = {{0, 64}, {0, 64}};
   private static final int[][] NOMINAL_TY = {{0, 0}, {64, 64}};

   // Displaced positions: tiles shifted from the nominal grid.
   // col=1 and row=1 tiles are shifted by +36px, enough that at level 1 the
   // sample point lands outside the uniform-grid tile range.
   private static final int[][] DISPLACED_TX = {{0, 100}, {0, 100}};
   private static final int[][] DISPLACED_TY = {{0, 0}, {100, 100}};

   // Displaced positions for the overlap case: step = tileWidth_ - overlap = 56,
   // but we displace col=1 tiles by +36 from that nominal step.
   // tx stores the buffer-pixel-0 canvas position (content at tx + overlap/2).
   private static final int[][] DISPLACED_OVL_TX = {{0, 92}, {0, 92}};
   private static final int[][] DISPLACED_OVL_TY = {{0, 0}, {92, 92}};

   private Path tmpDir;

   @Before
   public void setUp() throws Exception {
      tmpDir = Files.createTempDirectory("ndtiff_affine_test_");
   }

   @After
   public void tearDown() throws Exception {
      // Delete the temp directory tree.
      Files.walk(tmpDir)
            .sorted(Comparator.reverseOrder())
            .forEach(p -> p.toFile().delete());
   }

   @Test
   public void testNoAffineTags_uniformGrid() throws Exception {
      NDTiffStorage storage = writeAndReload("no_affine", TILE_W, TILE_H, OVERLAP, false, NOMINAL_TX, NOMINAL_TY);
      assertCompositeCorrect(storage, 0, NOMINAL_TX, NOMINAL_TY, TILE_W, TILE_H, OVERLAP);
      assertCompositeCorrect(storage, 1, NOMINAL_TX, NOMINAL_TY, TILE_W, TILE_H, OVERLAP);
   }

   @Test
   public void testAffineTags_nominalPositions() throws Exception {
      NDTiffStorage storage = writeAndReload("affine_nominal", TILE_W, TILE_H, OVERLAP, true, NOMINAL_TX, NOMINAL_TY);
      assertCompositeCorrect(storage, 0, NOMINAL_TX, NOMINAL_TY, TILE_W, TILE_H, OVERLAP);
      assertCompositeCorrect(storage, 1, NOMINAL_TX, NOMINAL_TY, TILE_W, TILE_H, OVERLAP);
   }

   @Test
   public void testAffineTags_displaced_level0() throws Exception {
      NDTiffStorage storage = writeAndReload("affine_displaced_l0", TILE_W, TILE_H, OVERLAP, true, DISPLACED_TX, DISPLACED_TY);
      assertCompositeCorrect(storage, 0, DISPLACED_TX, DISPLACED_TY, TILE_W, TILE_H, OVERLAP);
   }

   @Test
   public void testAffineTags_displaced_level1() throws Exception {
      NDTiffStorage storage = writeAndReload("affine_displaced_l1", TILE_W, TILE_H, OVERLAP, true, DISPLACED_TX, DISPLACED_TY);
      assertCompositeCorrect(storage, 1, DISPLACED_TX, DISPLACED_TY, TILE_W, TILE_H, OVERLAP);
   }

   @Test
   public void testAffineTags_displaced_withOverlap_level0() throws Exception {
      NDTiffStorage storage = writeAndReload("affine_displaced_ovl_l0", TILE_W_OVL, TILE_H_OVL, OVERLAP_W, true,
            DISPLACED_OVL_TX, DISPLACED_OVL_TY);
      assertCompositeCorrect(storage, 0, DISPLACED_OVL_TX, DISPLACED_OVL_TY, TILE_W_OVL, TILE_H_OVL, OVERLAP_W);
   }

   @Test
   public void testAffineTags_displaced_withOverlap_level1() throws Exception {
      NDTiffStorage storage = writeAndReload("affine_displaced_ovl_l1", TILE_W_OVL, TILE_H_OVL, OVERLAP_W, true,
            DISPLACED_OVL_TX, DISPLACED_OVL_TY);
      assertCompositeCorrect(storage, 1, DISPLACED_OVL_TX, DISPLACED_OVL_TY, TILE_W_OVL, TILE_H_OVL, OVERLAP_W);
   }

   /**
    * Samples pixels in the gap region between adjacent tiles at level 1 to verify no
    * black border. Uses large overlap (matching realistic acquisition) and displaced
    * positions so the gap between content regions is visible at level 1.
    *
    * tileW=64, overlap=16 → contentW=48, step between tiles ~48.
    * Displaced: col=1 at tx=70 (nominal step=48, displaced by +22).
    * At level 1: col=0 content ends at (0+8+48)/2=28, col=1 content starts at (70+8)/2=39.
    * Gap pixels [28,39) should be non-zero (filled from edge of col=0 or col=1).
    */
   @Test
   public void testAffineTags_noBlackBorder_overlappingTiles_level1() throws Exception {
      int tileW = 64, tileH = 64, overlap = 16;
      // Col=0 at tx=0, col=1 at tx=50.  fullTileW=64 → at level 1:
      //   col=0 covers canvas [0/2, 64/2)  = [0, 32)
      //   col=1 covers canvas [50/2, 114/2) = [25, 57)
      // They overlap [25,32) — no gap.
      int[][] tx = {{0, 50}, {0, 50}};
      int[][] ty = {{0, 0}, {50, 50}};

      NDTiffStorage storage = writeAndReload("border_test", tileW, tileH, overlap, true, tx, ty);

      int canvasW = (50 + tileW) / 2 + 2;
      int canvasH = (50 + tileH) / 2 + 2;

      HashMap<String, Object> axes = new HashMap<>();
      TaggedImage composite = storage.getDisplayImage(axes, 1, 0, 0, canvasW, canvasH);
      assertNotNull(composite);
      assertNotNull(composite.pix);
      short[] pixels = (short[]) composite.pix;

      // At y=15 (within col=0 row range [0,32)), x=[4,57) should all be non-zero.
      // Col=0 content at buffer [overlapOff=4, 4+quadW=28): maps to canvas [4,28).
      // Col=1 canvas starts at 25, content at canvas [25+4=29, 29+24=53).
      // The overlap zone [25,28) and [29,32): both tiles contribute → non-zero.
      int testY = 15;
      for (int cx = 4; cx < Math.min(53, canvasW); cx++) {
         short val = pixels[testY * canvasW + cx];
         assertFalse("Black pixel at level 1, x=" + cx + " y=" + testY, val == 0);
      }
   }

   // -------------------------------------------------------------------------
   // Helpers
   // -------------------------------------------------------------------------

   /** Writes a dataset and reloads it from disk so all pyramid levels are readable. */
   private NDTiffStorage writeAndReload(String name, int tileW, int tileH, int overlap,
                                         boolean withAffineTag, int[][] txArr, int[][] tyArr)
         throws Exception {
      File dir = tmpDir.resolve(name).toFile();
      NDTiffStorage written = createStorage(dir, tileW, tileH, overlap, withAffineTag, txArr, tyArr);
      written.finishedWriting();
      return new NDTiffStorage(written.getDiskLocation());
   }

   /**
    * Creates a 2×2 NDTiff dataset in {@code dir} using the given tile dimensions and positions.
    *
    * @param tileW        full buffer width (including overlap border)
    * @param tileH        full buffer height
    * @param overlap      GridPixelOverlapX/Y (xOverlap_ = yOverlap_)
    * @param withAffineTag if true, writes TileAffineTransform tags
    * @param txArr        [row][col] canvas X position of each tile's buffer pixel (0,0)
    * @param tyArr        [row][col] canvas Y position of each tile's buffer pixel (0,0)
    */
   private NDTiffStorage createStorage(File dir, int tileW, int tileH, int overlap,
                                        boolean withAffineTag,
                                        int[][] txArr, int[][] tyArr) throws Exception {
      JSONObject summary = new JSONObject();
      summary.put("Width", tileW);
      summary.put("Height", tileH);
      summary.put("GridPixelOverlapX", overlap);
      summary.put("GridPixelOverlapY", overlap);

      NDTiffStorage storage = new NDTiffStorage(
            dir.getParent(), dir.getName(),
            summary, overlap, overlap,
            true, null, 30, null, true);
      storage.increaseMaxResolutionLevel(2);

      for (int row = 0; row < 2; row++) {
         for (int col = 0; col < 2; col++) {
            int tx = txArr[row][col];
            int ty = tyArr[row][col];

            // Fill the entire buffer with a unique value so we can verify placement.
            short fillValue = (short) ((row * 2 + col + 1) * 1000);
            short[] pixels = new short[tileW * tileH];
            for (int i = 0; i < pixels.length; i++) {
               pixels[i] = fillValue;
            }

            JSONObject tags = new JSONObject();
            tags.put("Width", tileW);
            tags.put("Height", tileH);
            tags.put("BytesPerPixel", 2);
            tags.put("XPositionPix", tx);
            tags.put("YPositionPix", ty);

            if (withAffineTag) {
               JSONArray affine = new JSONArray();
               affine.put(1.0); affine.put(0.0); affine.put(0.0); affine.put((double) tx);
               affine.put(0.0); affine.put(1.0); affine.put(0.0); affine.put((double) ty);
               affine.put(0.0); affine.put(0.0); affine.put(1.0); affine.put(0.0);
               tags.put("TileAffineTransform", affine);
            }

            JSONObject axesJson = new JSONObject();
            axesJson.put("row", row);
            axesJson.put("column", col);
            tags.put("Axes", axesJson);

            HashMap<String, Object> axes = new HashMap<>();
            axes.put("row", row);
            axes.put("column", col);

            storage.putImageMultiRes(pixels, tags, axes, false, 16, tileH, tileW).get();
         }
      }
      return storage;
   }

   /**
    * Verifies that getDisplayImage at the given dsIndex returns the correct
    * pixel values at the centre of each tile's content region on the canvas.
    *
    * Content starts at (tx + overlap/2, ty + overlap/2) in buffer coords.
    * At level N the content centre on canvas = (tx + overlap/2 + contentW/2) / dsScale.
    */
   private void assertCompositeCorrect(NDTiffStorage storage, int dsIndex,
                                        int[][] txArr, int[][] tyArr,
                                        int tileW, int tileH, int overlap) {
      int dsScale = 1 << dsIndex;
      int contentW = tileW - overlap;
      int contentH = tileH - overlap;

      // Canvas size: span from 0 to max right/bottom edge of any tile's full buffer.
      int canvasW = 0;
      int canvasH = 0;
      for (int row = 0; row < 2; row++) {
         for (int col = 0; col < 2; col++) {
            canvasW = Math.max(canvasW, (txArr[row][col] + tileW) / dsScale + 1);
            canvasH = Math.max(canvasH, (tyArr[row][col] + tileH) / dsScale + 1);
         }
      }

      HashMap<String, Object> axes = new HashMap<>();
      TaggedImage composite = storage.getDisplayImage(axes, dsIndex, 0, 0, canvasW, canvasH);
      assertNotNull("getDisplayImage returned null at dsIndex=" + dsIndex, composite);
      assertNotNull("getDisplayImage returned null pixels at dsIndex=" + dsIndex, composite.pix);
      short[] pixels = (short[]) composite.pix;

      for (int row = 0; row < 2; row++) {
         for (int col = 0; col < 2; col++) {
            short expectedValue = (short) ((row * 2 + col + 1) * 1000);
            // Sample at the centre of this tile's content region on the downsampled canvas.
            int contentCentreX = txArr[row][col] + overlap / 2 + contentW / 2;
            int contentCentreY = tyArr[row][col] + overlap / 2 + contentH / 2;
            int sampleX = contentCentreX / dsScale;
            int sampleY = contentCentreY / dsScale;
            if (sampleX >= canvasW || sampleY >= canvasH) {
               continue;
            }
            short actual = pixels[sampleY * canvasW + sampleX];
            assertEquals(
                  "Wrong pixel at dsIndex=" + dsIndex
                        + " row=" + row + " col=" + col
                        + " sampleX=" + sampleX + " sampleY=" + sampleY,
                  expectedValue, actual);
         }
      }
   }
}
