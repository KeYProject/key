package org.key_project.jmlediting.core.dom.internal;

import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;

/**
 * Implements a {@link PrimitiveNode} without any children.
 *
 * @author Moritz Lichter
 *
 */
public abstract class PrimitiveNode extends AbstractASTNode {

   /**
    * Creates a new {@link PrimitiveNode}. StartOffset needs to be less than
    * endOffset.
    *
    * @param startOffset
    *           the start offset of the node
    * @param endOffset
    *           the end offset of the node
    */
   public PrimitiveNode(final int startOffset, final int endOffset) {
      super(startOffset, endOffset);
   }

   @Override
   public List<IASTNode> getChildren() {
      return Collections.emptyList();
   }

   // Overrides for performance

   @Override
   public <T> T search(final INodeSearcher<T> searcher) {
      return searcher.searchNode(this);
   };

   @Override
   public <T> T traverse(final INodeTraverser<T> traverser, final T init) {
      return traverser.traverse(this, init);
   }
}
