package org.key_project.jmlediting.core.parser.internal;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;

public abstract class AbstractASTNode implements IASTNode {

   @Override
   public <T> T serach(final INodeSearcher<T> searcher) {
      List<IASTNode> children = this.getChildren();
      if (children.isEmpty()) {
         return searcher.searchNode(this);
      }
      IASTNode selectedChild = searcher.selectChild(getChildren());
      if (selectedChild == null) {
         return searcher.searchNode(this);
      }
      return  selectedChild.serach(searcher);
   }

}
