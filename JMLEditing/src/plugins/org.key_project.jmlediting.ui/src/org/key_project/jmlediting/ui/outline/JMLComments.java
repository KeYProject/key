package org.key_project.jmlediting.ui.outline;

import java.util.List;

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
   private final String text;
   private final int startOffset;
   private final int endOffset;

   /**
    * 
    * @param commenttext The Text that should be shown in the Outline.
    * @param startOffset The start offset.
    * @param endOffset The end offset.
    */
   public JMLComments(String commenttext, int startOffset, int endOffset) {
      this.text = commenttext;
      this.startOffset = startOffset;
      this.endOffset = endOffset;
   }

   @Override
   public final String toString() {
      return text;
   }

   @Override
   public final int getStartOffset() {
      return startOffset;
   }

   @Override
   public final int getEndOffset() {
      return endOffset;
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
