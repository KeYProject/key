package org.key_project.jmlediting.core.dom;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.key_project.jmlediting.core.dom.internal.ASTNode;
import org.key_project.jmlediting.core.dom.internal.KeywordNode;
import org.key_project.jmlediting.core.dom.internal.StringNode;
import org.key_project.jmlediting.core.dom.internal.UnparsedTextNode;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public final class Nodes {

   public static IASTNode createNode(final int startOffset,
         final int endOffset, final int type, final IASTNode... children) {
      return new ASTNode(startOffset, endOffset, type, Arrays.asList(children));
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

   public static IASTNode createString(final int startOffset,
         final int endOffset, final String content) {
      return new StringNode(startOffset, endOffset, content);
   }

   public static IASTNode createList(final IASTNode... children) {
      return createNode(NodeTypes.LIST, children);
   }

   public static IASTNode createList(final List<IASTNode> children) {
      return createNode(NodeTypes.LIST, children);
   }

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

   public static boolean isString(final IASTNode node) {
      return node.getType() == NodeTypes.STRING;
   }

   public static boolean isKeyword(final IASTNode node) {
      return node.getType() == NodeTypes.KEYWORD;
   }

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

   public static IKeyword getKeywordNode(final IASTNode node, final int position) {
      final IASTNode keywordApplNode = getNodeAtPosition(node, position,
            NodeTypes.KEYWORD_APPL);
      if (keywordApplNode == null) {
         return null;
      }
      final IASTNode keywordNode = keywordApplNode.getChildren().get(0);
      if (Nodes.isKeyword(keywordNode)) {
         return ((IKeywordNode) keywordNode).getKeyword();
      }
      return null;

   }

}
