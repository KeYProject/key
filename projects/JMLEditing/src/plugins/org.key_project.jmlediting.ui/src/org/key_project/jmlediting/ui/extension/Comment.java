package org.key_project.jmlediting.ui.extension;

public class Comment {

   int offset;
   int length;
   
   public Comment(int offset, int length){
      this.offset=offset;
      this.length=length;
   }
   
   public int getLength() {
      return length;
   }
   
   public int getOffset() {
      return offset;
   }
}
