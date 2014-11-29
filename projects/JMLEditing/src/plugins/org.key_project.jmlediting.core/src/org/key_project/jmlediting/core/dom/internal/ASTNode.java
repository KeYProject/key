package org.key_project.jmlediting.core.dom.internal;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;

public class ASTNode extends AbstractASTNode{
   
   private final int type;
   private final int startOffset;
   private final int endOffset;
   private List<IASTNode> children;
   
   public ASTNode(int startOffset, int endOffset, int type, List<IASTNode> children) {
      super();
      this.startOffset = startOffset;
      this.endOffset = endOffset;
      this.type = type;
      this.children = children;
   }
   
   @Override
   public int getStartOffset() {
      return this.startOffset;
   }
   
   @Override
   public int getEndOffset() {
      return this.endOffset;
   }

   @Override
   public int getType() {
      return this.type;
   }

   @Override
   public List<IASTNode> getChildren() {
      if (this.children == null) {
         return Collections.emptyList();
      } else {
         return Collections.unmodifiableList(this.children);
      }
   }
   
   public void addChildren(IASTNode node) {
      if (this.children == null) {
         this.children = new ArrayList<IASTNode>(2);
      }
      this.children.add(node);
   }
   
   

}
