package org.key_project.jmlediting.core.parser;

import static org.junit.Assert.assertEquals;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;

public class DomCompareUtils {

   public static void compareIASTNode(IASTNode n1, IASTNode n2,
         boolean checkOffsets) {
      if (checkOffsets) {
         assertEquals("Start offset not equals", n1.getStartOffset(),
               n2.getStartOffset());
         assertEquals("End offset not equals", n1.getEndOffset(),
               n2.getEndOffset());
      }
      assertEquals("Type not equals", n1.getType(), n2.getType());
      assertEquals("Number of children not equals", n1.getChildren().size(), n2
            .getChildren().size());

      switch (n1.getType()) {
      case NodeTypes.STRING:
         assertEquals("String content not equals",
               ((IStringNode) n1).getString(), ((IStringNode) n2).getString());
         break;
      case NodeTypes.KEYWORD:
         assertEquals("Keyword instance not equal",
               ((IKeywordNode) n1).getKeywordInstance(),
               ((IKeywordNode) n2).getKeywordInstance());
         assertEquals("Keyword not equal", ((IKeywordNode) n1).getKeyword(),
               ((IKeywordNode) n2).getKeyword());
         break;
      }

      for (int i = 0; i < n1.getChildren().size(); i++) {
         compareIASTNode(n1.getChildren().get(i), n2.getChildren().get(i),
               checkOffsets);
      }
   }

}
