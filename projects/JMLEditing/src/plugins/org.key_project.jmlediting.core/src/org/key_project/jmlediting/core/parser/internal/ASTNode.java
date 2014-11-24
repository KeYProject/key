package org.key_project.jmlediting.core.parser.internal;

import org.key_project.jmlediting.core.dom.IASTNode;

public abstract class ASTNode implements IASTNode{
   
   private int startOffset;
   private int endOffset;
   
   public ASTNode(int startOffset, int endOffset) {
      super();
      this.startOffset = startOffset;
      this.endOffset = endOffset;
   }
   
   @Override
   public int getStartOffset() {
      return this.startOffset;
   }
   
   @Override
   public int getEndOffset() {
      return this.endOffset;
   }

}
