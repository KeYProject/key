package org.key_project.jmlediting.core.validation;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.internal.corext.dom.GenericVisitor;

public class JavaCodeVisitor extends GenericVisitor {
   private final int endOffsetOfComment;
   private ASTNode nodeAfterComment;
   private final int loopOffset;

   public JavaCodeVisitor(final int commentEndOffset, final int loopOffset) {
      this.endOffsetOfComment = commentEndOffset;
      this.loopOffset = loopOffset;
      this.nodeAfterComment = null;
   }

   public ASTNode getNodeAfterComment() {
      return this.nodeAfterComment;
   };

   @Override
   protected boolean visitNode(final ASTNode node) {
      if (node instanceof Comment) {
         return false;
      }
      if (node != null) {
         if (node.getStartPosition() > this.endOffsetOfComment
               && node.getStartPosition() < this.loopOffset) {
            if (this.nodeAfterComment != null) {
               if (node.getStartPosition() < this.nodeAfterComment
                     .getStartPosition()) {
                  this.nodeAfterComment = node;
                  return true;
               }
            }
            else {
               this.nodeAfterComment = node;
               return true;
            }
         }
      }
      return true;
   }
}
