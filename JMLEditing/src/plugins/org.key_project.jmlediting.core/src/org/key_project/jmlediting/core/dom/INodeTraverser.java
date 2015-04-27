package org.key_project.jmlediting.core.dom;

/**
 * A generic specification of a traverser of an AST.
 * 
 * @author Moritz Lichter
 *
 * @see IASTNode#traverse(INodeTraverser, Object)
 * @param <T>
 *           the result type of the traversal
 */
public interface INodeTraverser<T> {

   /**
    * Continues the traversal for the current node (not the subnodes).
    * 
    * @param node
    *           the current node to traverse
    * @param existing
    *           the traversal result for the nodes traversed before
    * @return the result of the traversal after traversing this node
    */
   T traverse(IASTNode node, T existing);

}
