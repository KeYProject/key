package org.key_project.jmlediting.ui.extension;

public class Comment {

   private final int offset;
   private final int end;

   private final int contentOffset;
   private final int contentEndOffset;

   public Comment(final int offset, final int end, final int contentOffset,
         final int contentEndOffset) {
      super();
      this.offset = offset;
      this.end = end;
      this.contentOffset = contentOffset;
      this.contentEndOffset = contentEndOffset;
   }

   public int getEnd() {
      return this.end;
   }

   public int getOffset() {
      return this.offset;
   }
}
