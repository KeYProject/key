package org.key_project.jmlediting.core.test.parser;

import static org.junit.Assert.assertEquals;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class DomCompareUtils {

   public static void compareIASTNode(final IASTNode n1, final IASTNode n2,
         final boolean checkOffsets) {
      if (checkOffsets) {
         assertEquals("Start offset not equals", n1.getStartOffset(),
               n2.getStartOffset());
         assertEquals("End offset not equals", n1.getEndOffset(),
               n2.getEndOffset());
      }
      assertEquals(
            "Type not equals, got " + NodeTypes.getTypeName(n2.getType())
                  + " but was " + NodeTypes.getTypeName(n1.getType()),
            n1.getType(), n2.getType());
      assertEquals("Number of children not equals", n1.getChildren().size(), n2
            .getChildren().size());

      if (Nodes.isString(n1)) {
         assertEquals("String content not equals",
               ((IStringNode) n1).getString(), ((IStringNode) n2).getString());
      }
      else if (Nodes.isKeyword(n1)) {
         assertEquals("Keyword instance not equal",
               ((IKeywordNode) n1).getKeywordInstance(),
               ((IKeywordNode) n2).getKeywordInstance());
         assertEquals("Keyword not equal", ((IKeywordNode) n1).getKeyword(),
               ((IKeywordNode) n2).getKeyword());
      }

      for (int i = 0; i < n1.getChildren().size(); i++) {
         compareIASTNode(n1.getChildren().get(i), n2.getChildren().get(i),
               checkOffsets);
      }
   }

}
