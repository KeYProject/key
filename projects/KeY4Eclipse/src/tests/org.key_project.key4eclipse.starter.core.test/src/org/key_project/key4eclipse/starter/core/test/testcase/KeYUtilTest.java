package org.key_project.key4eclipse.starter.core.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * Tests for {@link KeYUtil}
 * @author Martin Hentschel
 */
public class KeYUtilTest extends TestCase {
   /**
    * Tests {@link KeYUtil#normalizeRecorderColumn(int, int, int[])} and
    * {@link KeYUtil#normalizeRecorderColumn(int, int[])}.
    */
   @Test
   public void testNormalizeRecorderColumn() {
      // Test invalid parameters
      assertEquals(-1, KeYUtil.normalizeRecorderColumn(-1, 4, new int[] {0}));
      assertEquals(1, KeYUtil.normalizeRecorderColumn(1, 0, new int[] {0}));
      assertEquals(1, KeYUtil.normalizeRecorderColumn(1, 1, new int[] {0}));
      assertEquals(1, KeYUtil.normalizeRecorderColumn(1, 4, null));
      // Test one tab
      doTestNormalizeRecorderColumn("\tABCDEF");
      doTestNormalizeRecorderColumn("A\tBCDEF");
      doTestNormalizeRecorderColumn("AB\tCDEF");
      doTestNormalizeRecorderColumn("ABC\tDEF");
      doTestNormalizeRecorderColumn("ABCD\tEF");
      doTestNormalizeRecorderColumn("ABCDE\tF");
      doTestNormalizeRecorderColumn("ABCDEF\t");
      // Test two tabs
      doTestNormalizeRecorderColumn("\t\tABCDEF");
      doTestNormalizeRecorderColumn("\tA\tBCDEF");
      doTestNormalizeRecorderColumn("\tAB\tCDEF");
      doTestNormalizeRecorderColumn("\tABC\tDEF");
      doTestNormalizeRecorderColumn("\tABCD\tEF");
      doTestNormalizeRecorderColumn("\tABCDE\tF");
      doTestNormalizeRecorderColumn("\tABCDEF\t");
      doTestNormalizeRecorderColumn("A\t\tBCDEF");
      doTestNormalizeRecorderColumn("A\tB\tCDEF");
      doTestNormalizeRecorderColumn("A\tBC\tDEF");
      doTestNormalizeRecorderColumn("A\tBCD\tEF");
      doTestNormalizeRecorderColumn("A\tBCDE\tF");
      doTestNormalizeRecorderColumn("A\tBCDEF\t");
      doTestNormalizeRecorderColumn("AB\t\tCDEF");
      doTestNormalizeRecorderColumn("AB\tC\tDEF");
      doTestNormalizeRecorderColumn("AB\tCD\tEF");
      doTestNormalizeRecorderColumn("AB\tCDE\tF");
      doTestNormalizeRecorderColumn("AB\tCDEF\t");
      doTestNormalizeRecorderColumn("ABC\t\tDEF");
      doTestNormalizeRecorderColumn("ABC\tD\tEF");
      doTestNormalizeRecorderColumn("ABC\tDE\tF");
      doTestNormalizeRecorderColumn("ABC\tDEF\t");
      doTestNormalizeRecorderColumn("ABCD\t\tEF");
      doTestNormalizeRecorderColumn("ABCD\tE\tF");
      doTestNormalizeRecorderColumn("ABCD\tEF\t");
      doTestNormalizeRecorderColumn("ABCDE\t\tF");
      doTestNormalizeRecorderColumn("ABCDE\tF\t");
      doTestNormalizeRecorderColumn("ABCDEF\t\t");
      // Test three tabs
      doTestNormalizeRecorderColumn("\t\t\tABCDEF");
      doTestNormalizeRecorderColumn("A\tBC\tDE\tF");
      doTestNormalizeRecorderColumn("ABC\tD\t\tEF");
      doTestNormalizeRecorderColumn("AB\t\t\tCDEF");
      doTestNormalizeRecorderColumn("ABCDEF\t\t\t");
   }
   
   /**
    * Executes a test case for {@link #testNormalizeColumn()}.
    * @param text The text to test.
    */
   protected void doTestNormalizeRecorderColumn(String text) {
      for (int tabSize = 1; tabSize <= KeYUtil.RECORDER_TAB_SIZE; tabSize++) {
         doTestNormalizeRecorderColumn(text, tabSize);
      }
   }
   
   /**
    * Executes a test case for {@link #testNormalizeColumn()}.
    * @param text The text to test.
    * @param tabSize The tab size to use.
    */
   protected void doTestNormalizeRecorderColumn(String text, int tabSize) {
      assertNotNull(text);
      // Compute tab indices
      int[] tabIndices = new int[0];
      int tabIndex = text.indexOf('\t');
      while (tabIndex >= 0) {
         tabIndices = ArrayUtil.add(tabIndices, tabIndex);
         tabIndex = text.indexOf('\t', tabIndex + 1);
      }
      // Test normalization
      char[] signs = text.toCharArray();
      int column = 0;
      int expectedNoramlizedColumn = 0;
      for (char sign : signs) {
         int actualNormalizedColumn = KeYUtil.normalizeRecorderColumn(column, tabSize, tabIndices);
         assertEquals(expectedNoramlizedColumn, actualNormalizedColumn);
         if (tabSize == KeYUtil.RECORDER_TAB_SIZE) {
            actualNormalizedColumn = KeYUtil.normalizeRecorderColumn(column, tabIndices);
            assertEquals(expectedNoramlizedColumn, actualNormalizedColumn);
         }
         // Update columns
         switch (sign) {
            case '\t' : column += (tabSize - (column % tabSize));
                        break;
            default : column ++;
         }
         expectedNoramlizedColumn ++;
      }
   }
   
   /**
    * Tests {@link KeYUtil#isFileExtensionSupported(String)}.
    */
   @Test
   public void testIsFileExtensionSupported() {
      assertFalse(KeYUtil.isFileExtensionSupported(null));
      assertFalse(KeYUtil.isFileExtensionSupported("INVALID_EXTENSION"));
      assertTrue(KeYUtil.isFileExtensionSupported(KeYUtil.KEY_FILE_EXTENSION));
      assertTrue(KeYUtil.isFileExtensionSupported(KeYUtil.PROOF_FILE_EXTENSION));
   }
}
