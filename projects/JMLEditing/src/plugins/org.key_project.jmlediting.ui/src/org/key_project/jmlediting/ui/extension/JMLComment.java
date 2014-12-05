package org.key_project.jmlediting.ui.extension;

public class JMLComment {

   // All offsets are inclusive

   private final int beginOffset;
   private final int endOffset;

   private final int contentBeginOffset;
   private final int contentEndOffset;

   public JMLComment(final int offset, final int end, final int contentOffset,
         final int contentEndOffset) {
      super();
      this.beginOffset = offset;
      this.endOffset = end;
      this.contentBeginOffset = contentOffset;
      this.contentEndOffset = contentEndOffset;
   }

   public int getEndOffset() {
      return this.endOffset;
   }

   public int getBeginOffset() {
      return this.beginOffset;
   }

   public int getContentBeginOffset() {
      return this.contentBeginOffset;
   }

   public int getContentEndOffset() {
      return this.contentEndOffset;
   }

   public int getLength() {
      // Need to add one because end offset is inclusive
      return this.getEndOffset() - this.getBeginOffset() + 1;
   }

   public int getContentLength() {
      return this.getContentEndOffset() - this.getContentBeginOffset() + 1;
   }
}
