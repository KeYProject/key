package org.key_project.jmlediting.profile.jmlref.test.utilities;

import static org.junit.Assert.fail;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.test.utilities.DomCompareUtils;

public class DomBuildUtils {

   public static IASTNode buildKeywordSequence(final int start, final int end,
         final IASTNode... nodes) {
      return Nodes.createNode(start, end, NodeTypes.NODE, nodes);
   }

   public static IASTNode buildKeywordSpec(final String keyword, final String content) {
      return buildKeywordSpec(keyword, 0, 0, content);
   }

   public static IASTNode buildKeywordSpec(final String keyword, final int start) {
      IKeyword sKeyword = null;
      for (final IKeyword k : ProfileWrapper.testProfile.getSupportedKeywords()) {
         if (k.getKeywords().contains(keyword)) {
            sKeyword = k;
            break;
         }
      }
      if (sKeyword == null) {
         fail("Unable to find keyword");
      }
      return Nodes.createKeyword(start, start + keyword.length(), sKeyword,
            keyword);

   }

   public static IASTNode buildKeywordSpec(final String keyword, final int start,
         final int end, final String content) {
      IKeyword sKeyword = null;
      for (final IKeyword k : ProfileWrapper.testProfile.getSupportedKeywords()) {
         if (k.getKeywords().contains(keyword)) {
            sKeyword = k;
            break;
         }
      }
      if (sKeyword == null) {
         fail("Unable to find keyword");
      }

      IASTNode contentNode;
      final int contentStart = start + keyword.length() + 1;
      final int contentEnd = end - 1;
      if (content == null) {
         contentNode = Nodes.createNode(contentStart, contentEnd,
               DomCompareUtils.WILDCARD_TYPE);
      }
      else {
         contentNode = Nodes.createString(contentStart, contentEnd, content);
      }

      return Nodes.createNode(start, end, NodeTypes.KEYWORD_APPL, Nodes
            .createKeyword(start, start + keyword.length(), sKeyword, keyword),
            Nodes.createNode(start + keyword.length() + 1, end,
                  NodeTypes.KEYWORD_CONTENT, contentNode));
   }
}
