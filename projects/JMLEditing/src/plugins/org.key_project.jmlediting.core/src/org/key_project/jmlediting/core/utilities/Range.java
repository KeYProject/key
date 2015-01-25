/**
 *
 */
package org.key_project.jmlediting.core.utilities;

/**
 * @author David Giessing Class to store the offset and the length of a
 *         Substring in a String
 */
public class Range {
   /**
    * The offset where the Substring starts.
    */
   private final int offset;

   /**
    * The length of the Substring.
    */
   private final int length;

   /**
    * Creates a new Range Object.
    *
    * @param offset
    *           The offset where the Substring starts
    * @param length
    *           the length of the Substring
    */
   public Range(final int offset, final int length) {
      this.offset = offset;
      this.length = length;
   }

   /**
    * @return the offset
    */
   public int getOffset() {
      return this.offset;
   }

   /**
    * @return the length
    */
   public int getLength() {
      return this.length;
   }

}
