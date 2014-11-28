package org.key_project.jmlediting.core.parser.internal;

import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;

public abstract class PrimitiveNode extends AbstractASTNode {

   private final int startOffset;
   private final int endOffset;

   public PrimitiveNode(int startOffset, int endOffset) {
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

   @Override
   public List<IASTNode> getChildren() {
      return Collections.emptyList();
   }

   public <T> T serach(INodeSearcher<T> searcher) {
      return searcher.searchNode(this);
   };
}
