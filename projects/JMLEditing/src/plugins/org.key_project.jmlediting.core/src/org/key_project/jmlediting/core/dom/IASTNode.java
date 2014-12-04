package org.key_project.jmlediting.core.dom;

import java.util.List;

/**
 * This class specifies a general AST node for JML.
 * 
 * @author Moritz Lichter
 *
 */
public interface IASTNode {

   /**
    * Returns the start offset in the parsed text for the content of the AST
    * node. The start offset must be less than or smaller than the start offset
    * for all children.
    * 
    * @return the start offset in the parsed text
    */
   int getStartOffset();

   /**
    * Returns the end offset in the parsed text for the content of the AST node.
    * The end offset must be greater or equal to the start offsets for all
    * children.
    * 
    * @return the end offset in the parsed text
    */
   int getEndOffset();

   /**
    * Returns the type of the node.
    * 
    * @return the type of this node
    */
   int getType();

   /**
    * Returns a list for all children of this node. The children are not allowed
    * to have overlapping start and end offsets. Also they need to be ordered.
    * The end offset of the child at position i is less than the start offset of
    * the child at position i +1. This list must not be modified and is
    * guaranteed not the be null (but maybe empty).
    * 
    * @return the list of all children
    */
   List<IASTNode> getChildren();

   /**
    * Searches to this node and to all children. If this method has no children,
    * this method returns the result of calling
    * {@link INodeSearcher#searchNode(IASTNode)}. Otherwise the searcher is
    * first asked to select a child note to continue searching using
    * {@link INodeSearcher#selectChild(List)}. If the result it not null, search
    * is continued in this child. Otherwise, the result of
    * {@link INodeSearcher#searchNode(IASTNode)} for this node is returned.
    * 
    * @param <T>
    *           the result type of the search
    * @param searcher
    *           the searcher object to search through the AST
    * @return the search result from the searcher
    */
   <T> T serach(INodeSearcher<T> searcher);

   /**
    * Traverses the AST tree bottom up from left to right. The
    * {@link INodeTraverser#traverse(IASTNode, Object)} is invoked during the
    * traversal. The second parameter value is init for the first call,
    * otherwise the result from the other calls.
    * 
    * @param <T>
    *           the result type of the traversal
    * @param traverser
    *           the traverser to traverse the tree
    * @param init
    *           the initial value of the traverser
    * @return the result of the traversal
    */
   <T> T traverse(INodeTraverser<T> traverser, T init);

}
