package org.key_project.jmlediting.core.dom.internal;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * Abstract implementation of the {@link IASTNode} which implements common
 * functionality.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractASTNode implements IASTNode {

   /**
    * The start offset (inclusive) of the node.
    */
   private final int startOffset;
   /**
    * The end offset (inclusive) of the node.
    */
   private final int endOffset;

   /**
    * Creates a new {@link AbstractASTNode}. StartOffset needs to be less than
    * or equal endOffset. An equal start and end node means that the node does
    * not cover anything (e.g. an empty list)
    *
    * @param startOffset
    *           the start offset of the node
    * @param endOffset
    *           the end offset of the node
    */
   public AbstractASTNode(final int startOffset, final int endOffset) {
      super();
      if (startOffset > endOffset) {
         throw new IllegalArgumentException("Offsets are invalid");
      }
      this.startOffset = startOffset;
      this.endOffset = endOffset;
   }

   @Override
   public <T> T serach(final INodeSearcher<T> searcher) {
      final List<IASTNode> children = this.getChildren();
      // No children -> search this
      if (children.isEmpty()) {
         return searcher.searchNode(this);
      }
      // Check where to continue
      final IASTNode selectedChild = searcher.selectChild(this.getChildren());
      // Do not continue -> search this
      if (selectedChild == null) {
         return searcher.searchNode(this);
      }
      // Search in child
      return selectedChild.serach(searcher);
   }

   @Override
   public <T> T traverse(final INodeTraverser<T> traverser, final T init) {
      T value = init;
      // Traverse children von left to right
      for (final IASTNode node : this.getChildren()) {
         value = node.traverse(traverser, value);
      }
      // Traverse me
      value = traverser.traverse(this, value);
      return value;
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
   public String toString() {
      String str = NodeTypes.getTypeName(this.getType()) + "["
            + this.getStartOffset() + "-" + this.getEndOffset() + "](";
      for (final IASTNode node : this.getChildren()) {
         str += node.toString() + ",";
      }
      str += ")";
      return str;
   }

}
