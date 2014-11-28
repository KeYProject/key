package org.key_project.jmlediting.core.dom;

import java.util.Arrays;
import java.util.List;

import org.key_project.jmlediting.core.parser.internal.ASTNode;
import org.key_project.jmlediting.core.parser.internal.KeywordNode;
import org.key_project.jmlediting.core.parser.internal.StringNode;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public final class Nodes {

   public static IASTNode createNode(int startOffset, int endOffset, int type,
         IASTNode... children) {
      return new ASTNode(startOffset, endOffset, type, Arrays.asList(children));
   }

   public static IASTNode createNode(int type, IASTNode... children) {
      return createNode(type, Arrays.asList(children));
   }

   public static IASTNode createNode(int type, List<IASTNode> children) {
      if (children == null || children.size() == 0) {
         throw new IllegalArgumentException(
               "Need to put at least one child node");
      }
      return new ASTNode(children.get(0).getStartOffset(), children.get(
            children.size() - 1).getEndOffset(), type, children);
   }

   public static IASTNode createString(int startOffset, int endOffset,
         String content) {
      return new StringNode(startOffset, endOffset, content);
   }

   public static IASTNode createKeyword(int startOffset, int endOffset,
         IKeyword keyword, String keywordInstance) {
      return new KeywordNode(startOffset, endOffset, keyword, keywordInstance);
   }
   
   public static boolean isString(IASTNode node) {
      return node.getType() == NodeTypes.STRING;
   }
   
   public static boolean isKeyword(IASTNode node) {
      return node.getType() == NodeTypes.KEYWORD;
   }

}
