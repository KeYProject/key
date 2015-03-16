package org.key_project.jmlediting.core.validation;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.BlockComment;
import org.eclipse.jdt.core.dom.LineComment;

public class CommentVisitor extends ASTVisitor {
   private final int offset;
   private final int endOffset;
   private ASTNode nodeCandidate;

   public CommentVisitor(final int offset, final int endOffset) {
      this.endOffset = endOffset;
      this.offset = offset;
      this.nodeCandidate = null;
   }

   public ASTNode getCorrespondingNode() {
      return this.nodeCandidate;
   }

   @Override
   public boolean visit(final BlockComment node) {
      System.out.println("Blockcomment Found");
      if (node.getStartPosition() <= this.offset
            && this.endOffset <= node.getStartPosition() + node.getLength()) {
         if (this.nodeCandidate != null
               && this.nodeCandidate.getLength() > node.getLength()) {
            this.nodeCandidate = node;
         }
      }
      return super.visit(node);
   }

   @Override
   public boolean visit(final LineComment node) {
      System.out.println("Linecomment Found");
      if (node.getStartPosition() <= this.offset
            && this.endOffset <= node.getStartPosition() + node.getLength()) {
         if (this.nodeCandidate != null
               && this.nodeCandidate.getLength() > node.getLength()) {
            this.nodeCandidate = node;
         }
      }
      return super.visit(node);
   }
}
