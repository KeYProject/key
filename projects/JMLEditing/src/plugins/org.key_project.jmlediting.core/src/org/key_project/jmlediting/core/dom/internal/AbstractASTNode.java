package org.key_project.jmlediting.core.dom.internal;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;

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
   
   @Override
   public <T> T traverse(final INodeTraverser<T> traverser, T init) {
      List<IASTNode> children = this.getChildren();
      if (children.isEmpty()) {
         return traverser.traverse(this, init);
      }
      T value = init;
      for (IASTNode node : this.getChildren()) {
         value = traverser.traverse(node, value);
      }
      value = traverser.traverse(this, value);
      return value;
   }

}
