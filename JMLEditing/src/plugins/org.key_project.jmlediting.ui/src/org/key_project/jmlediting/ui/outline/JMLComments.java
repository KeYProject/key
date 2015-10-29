package org.key_project.jmlediting.ui.outline;

import java.util.List;

import org.eclipse.jdt.core.dom.Comment;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;

/**
 * Contains {@link IASTNode} with a readable string that should be shown in the Outline.
 * 
 * @author Timm Lippert
 *
 */

public class JMLComments implements IASTNode {

   private Comment node;
   private String text;

   /**
    * 
    * @param commenttext The Text that should be shown in the Outline.
    * @param node The Comment {@link IASTNode}.
    * @param type type of the Comment.
    */

   public JMLComments(String commenttext, Comment node) {
      text = commenttext;
      this.node = node;
   }

   @Override
   public final String toString() {
      return text;
   }

   @Override
   public final int getStartOffset() {
      return node.getStartPosition();
   }

   @Override
   public final int getEndOffset() {
      return node.getLength() + node.getStartPosition();
   }

   @Override
   public final boolean containsOffset(int offset) {
      return false;
   }

   @Override
   public final boolean containsCaret(int caretPosition) {
      return false;
   }

   @Override
   public final int getType() {
      return 0;
   }

   @Override
   public final List<IASTNode> getChildren() {
      return null;
   }

   @Override
   public final <T> T search(INodeSearcher<T> searcher) {
      return null;
   }

   @Override
   public final <T> T traverse(INodeTraverser<T> traverser, T init) {
      return null;
   }

   @Override
   public final String prettyPrintAST() {
      return text;
   }
}
