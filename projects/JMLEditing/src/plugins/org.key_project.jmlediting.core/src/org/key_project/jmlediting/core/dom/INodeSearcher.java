package org.key_project.jmlediting.core.dom;

import java.util.List;

/**
 * Generic specification of a linear searcher through the AST. The searcher
 * consists of two methods: Selecting the next child in an AST node to continue
 * search and searching a node.
 * 
 * @author Moritz Lichter
 *
 * @see IASTNode#search(INodeSearcher)
 * @param <T>
 *           the result type of the search
 */
public interface INodeSearcher<T> {

   /**
    * Searches the given node (not the subnodes).
    * 
    * @param node
    *           the node to search
    * @return the result value
    */
   T searchNode(IASTNode node);

   /**
    * Selects the child of an IASTNode where to continue the search.
    * 
    * @param children
    *           the children to select one from
    * @return the selected child
    */
   IASTNode selectChild(List<IASTNode> children);

}
