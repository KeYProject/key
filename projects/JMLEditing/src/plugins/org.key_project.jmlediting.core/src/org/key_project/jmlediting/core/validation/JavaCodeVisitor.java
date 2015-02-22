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
      this.loopOffset = this.loopOffset;
      this.nodeAfterComment = null;
   }

   public ASTNode getNodeAfterComment() {
      return this.nodeAfterComment;
   };

   @Override
   protected boolean visitNode(final ASTNode node) {
      if (node instanceof Comment) {
         return super.visitNode(node);
      }
      if (node != null) {
         if (node.getStartPosition() > this.endOffsetOfComment
               && node.getStartPosition() < this.loopOffset) {
            if (this.nodeAfterComment != null) {
               if (node.getStartPosition() < this.nodeAfterComment
                     .getStartPosition()) {
                  this.nodeAfterComment = node;
                  return super.visitNode(node);
               }
            }
            else {
               this.nodeAfterComment = node;
               return super.visitNode(node);
            }
         }
      }
      return super.visitNode(node);
   }
}
