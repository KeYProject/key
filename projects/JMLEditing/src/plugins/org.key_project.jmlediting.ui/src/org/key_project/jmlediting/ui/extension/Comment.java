package org.key_project.jmlediting.ui.extension;

public class Comment {

   int offset;
   int end;

   public Comment(int offset, int length) {
      this.offset = offset;
      this.end = length;
   }

   public int getLength() {
      return end;
   }

   public int getOffset() {
      return end;
   }
}
