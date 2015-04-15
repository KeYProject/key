package org.key_project.jmlediting.core.dom;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.jmlediting.core.dom.internal.ASTNode;
import org.key_project.jmlediting.core.dom.internal.KeywordNode;
import org.key_project.jmlediting.core.dom.internal.StringNode;
import org.key_project.jmlediting.core.dom.internal.UnparsedTextNode;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public final class Nodes {

   /**
    * creates an IASTNode of Type type with startOffset, end Offset and Children
    * children.
    *
    * @param startOffset
    *           the startOffset of the new Node
    * @param endOffset
    *           the endOffset of the new Node
    * @param type
    *           the Type for the new Node
    * @param children
    *           the children of the new Node
    * @return the new IASTNode
    */
   public static IASTNode createNode(final int startOffset,
         final int endOffset, final int type, final IASTNode... children) {
      return new ASTNode(startOffset, endOffset, type, Arrays.asList(children));
   }

   public static IASTNode createNode(final int startOffset,
         final int endOffset, final int type, final List<IASTNode> children) {
      return new ASTNode(startOffset, endOffset, type, children);
   }

   public static IASTNode createNode(final int type, final IASTNode... children) {
      return createNode(type, Arrays.asList(children));
   }

   public static IASTNode createNode(final int type,
         final List<IASTNode> children) {
      if (children == null || children.size() == 0) {
         throw new IllegalArgumentException(
               "Need to put at least one child node");
      }
      return new ASTNode(children.get(0).getStartOffset(), children.get(
            children.size() - 1).getEndOffset(), type, children);
   }

   /**
    * Creates a new IASTNode from type StringNode from startOffset to endOffset
    * with Content content.
    *
    * @param startOffset
    *           the startOffset
    * @param endOffset
    *           the endOffset
    * @param content
    *           the content
    * @return the StringNode
    */
   public static IASTNode createString(final int startOffset,
         final int endOffset, final String content) {
      return new StringNode(startOffset, endOffset, content);
   }

   /**
    * Creates a IASTNode of Type List containing all given children.
    *
    * @param children
    *           the list of children to be contained in the List Node
    * @return the ListNode
    */
   public static IASTNode createList(final IASTNode... children) {
      return createNode(NodeTypes.LIST, children);
   }

   public static IASTNode createList(final List<IASTNode> children) {
      return createNode(NodeTypes.LIST, children);
   }

   /**
    * Creates a new KeywordNode from start to end offset with keyword keyword
    * and the concrete instance Keywordinstance.
    *
    * @param startOffset
    *           the startoffset
    * @param endOffset
    *           the endoffset
    * @param keyword
    *           the IKeyword
    * @param keywordInstance
    *           the concrete Keyword instance
    * @return the KeywordNode
    */
   public static IASTNode createKeyword(final int startOffset,
         final int endOffset, final IKeyword keyword,
         final String keywordInstance) {
      return new KeywordNode(startOffset, endOffset, keyword, keywordInstance);
   }

   public static IASTNode createOptional(final IASTNode node, final int nonePos) {
      if (node == null) {
         return createNode(nonePos, nonePos, NodeTypes.NONE);
      }
      else {
         return createNode(NodeTypes.SOME, node);
      }
   }

   public static IASTNode createUnparsedTextNode(final String text,
         final int startPos, final int endPos) {
      return new UnparsedTextNode(startPos, endPos, text);
   }

   public static IASTNode createErrorNode(final IASTNode... content) {
      return createNode(NodeTypes.ERROR_NODE, content);
   }

   /**
    * Creates a new error node
    * 
    * @param start
    *           startOffset
    * @param end
    *           endOffset
    * @param content
    *           the content of the ErrorNode
    * @return an ErrorNode
    */
   public static IASTNode createErrorNode(final int start, final int end,
         final IASTNode... content) {
      return createNode(start, end, NodeTypes.ERROR_NODE, content);
   }

   public static IASTNode createErrorNode(final int position) {
      return createNode(position, position, NodeTypes.ERROR_NODE);
   }

   public static boolean isString(final IASTNode node) {
      return node.getType() == NodeTypes.STRING;
   }

   public static boolean isKeyword(final IASTNode node) {
      return node.getType() == NodeTypes.KEYWORD;
   }

   /**
    * Returns the deepest node in node that contains position.
    *
    * @param position
    *           the position that has to be contained
    * @param node
    *           the AST to operate on
    * @return the deepest AST node that contains position, or null if node does
    *         not contain position.
    */
   public static IASTNode getDepthMostNodeWithPosition(final int position,
         final IASTNode node) {
      return node.search(new INodeSearcher<IASTNode>() {

         @Override
         public IASTNode searchNode(final IASTNode n) {
            if (n.getStartOffset() > position || n.getEndOffset() <= position) {
               return null;
            }
            for (final IASTNode node : n.getChildren()) {
               if (node.getStartOffset() <= position
                     && position < node.getEndOffset()) {
                  return null;
               }
            }
            return n;
         }

         @Override
         public IASTNode selectChild(final List<IASTNode> children) {
            return selectChildWithPosition(children, position);
         }
      });
   }

   public static IASTNode selectChildWithPosition(final IASTNode node,
         final int offset) {
      if (!node.containsOffset(offset)) {
         return null;
      }
      return selectChildWithPosition(node.getChildren(), offset);
   }

   private static IASTNode selectChildWithPosition(
         final List<IASTNode> children, final int offset) {
      for (final IASTNode node : children) {
         if (node.containsOffset(offset)) {
            return node;
         }
      }
      return null;
   }

   /**
    * Gets all IKeywordNodes from AST node.
    *
    * @param node
    *           the AST to operate on
    * @return a List of all IKeywordNodes in node or an empty List if there are
    *         none.
    */
   public static List<IKeywordNode> getAllKeywords(final IASTNode node) {
      return node.traverse(new INodeTraverser<List<IKeywordNode>>() {

         @Override
         public List<IKeywordNode> traverse(final IASTNode node,
               final List<IKeywordNode> existing) {
            if (node instanceof IKeywordNode) {
               existing.add((IKeywordNode) node);
            }
            return existing;
         }

      }, new LinkedList<IKeywordNode>());
   }

   /**
    * Returns a List of all Nodes of Type type in the AST node.
    *
    * @param node
    *           the ast to search in
    * @param type
    *           the desired Type
    * @return a List of Nodes of Type type in node or an empty List if there are
    *         none
    */
   public static List<IASTNode> getAllNodesOfType(final IASTNode node,
         final int type) {
      return node.traverse(new INodeTraverser<List<IASTNode>>() {

         @Override
         public List<IASTNode> traverse(final IASTNode node,
               final List<IASTNode> existing) {
            if (node.getType() == type) {
               existing.add(node);
            }
            return existing;
         }
      }, new LinkedList<IASTNode>());
   }

   /**
    * Returns the IASTNode of Type type at Position position, if there is one.
    * If not returns null.
    *
    * @param root
    *           the AST to operate on
    * @param position
    *           the searched position
    * @param type
    *           the desired type
    * @return an IASTNode of Type type at Position position if there is one,
    *         else null.
    */
   public static IASTNode getNodeAtPosition(final IASTNode root,
         final int position, final int type) {
      return root.search(new INodeSearcher<IASTNode>() {

         @Override
         public IASTNode searchNode(final IASTNode node) {
            if (node.getType() == type) {
               return node;
            }
            return null;
         }

         @Override
         public IASTNode selectChild(final List<IASTNode> children) {
            for (final IASTNode node : children) {
               if (node.getStartOffset() <= position
                     && position < node.getEndOffset()) {
                  return node;
               }
            }
            return null;
         }
      });
   }

   /**
    * Selects the topmost node with the given type that satisfies the following
    * condition: The caretPosition is on the node, so after a character that
    * belongs to the node, or at the whitespaces at the right of the node, so
    * after a character that belongs to this node and before a character that
    * belongs to the next right node which has the same parent.
    *
    * @param root
    *           the root node to start search at
    * @param caretPosition
    *           the caret position
    * @param type
    *           the type of node for which is searched
    * @return the node found or null if no node was found
    */
   public static IASTNode getNodeAtCaretPositionIncludeRightWhiteSpace(
         final IASTNode root, final int caretPosition, final int type) {
      final int cleanedCaretPosition = Math.min(root.getEndOffset(),
            caretPosition);
      return root.search(new INodeSearcher<IASTNode>() {

         @Override
         public IASTNode searchNode(final IASTNode node) {
            if (node.getType() == type) {
               return node;
            }
            return null;
         }

         @Override
         public IASTNode selectChild(final List<IASTNode> children) {
            if (children.isEmpty()) {
               return null;
            }
            final Iterator<IASTNode> childIterator = children.iterator();
            IASTNode node = childIterator.next();
            IASTNode nextNode = node;
            while (childIterator.hasNext()) {
               // Check whether is is a next node
               nextNode = childIterator.next();
               // Check whether the caret is valid
               if (node.getStartOffset() < cleanedCaretPosition
                     && cleanedCaretPosition <= nextNode.getStartOffset()) {
                  return node;
               }
               // Go to next node
               node = nextNode;
            }
            // Last node
            // Can only look into this node
            if (node.getStartOffset() < cleanedCaretPosition
                  && cleanedCaretPosition <= node.getEndOffset()) {
               return node;
            }
            return null;
         }
      });
   }

}
