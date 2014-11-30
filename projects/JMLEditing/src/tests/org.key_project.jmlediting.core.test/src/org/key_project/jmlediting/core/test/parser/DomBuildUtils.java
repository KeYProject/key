package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.fail;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class DomBuildUtils {

   static IASTNode buildKeywordSequence(final int start, final int end,
         final IASTNode... nodes) {
      return Nodes.createNode(start, end, NodeTypes.NODE, nodes);
   }

   static IASTNode buildKeywordSpec(final String keyword, final String content) {
      return buildKeywordSpec(keyword, 0, 0, content);
   }

   static IASTNode buildKeywordSpec(final String keyword, final int start) {
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

   static IASTNode buildKeywordSpec(final String keyword, final int start,
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
      return Nodes.createNode(start, end, NodeTypes.KEYWORD_APPL, Nodes
            .createKeyword(start, start + keyword.length(), sKeyword, keyword),
            Nodes.createNode(NodeTypes.NODE, Nodes.createString(
                  start + keyword.length() + 1, end, content)));
   }
}
