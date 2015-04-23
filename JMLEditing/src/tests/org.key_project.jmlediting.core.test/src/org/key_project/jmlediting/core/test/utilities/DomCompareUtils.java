package org.key_project.jmlediting.core.test.utilities;

import static org.junit.Assert.assertEquals;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class DomCompareUtils {

   public static final int WILDCARD_TYPE = NodeTypes
         .getNewType("CompareWildcardType");

   public static void compareIASTNode(final IASTNode expected,
         final IASTNode actual, final boolean checkOffsets) {
      if (checkOffsets) {
         assertEquals("Start offset not equals", expected.getStartOffset(),
               actual.getStartOffset());
         assertEquals("End offset not equals", expected.getEndOffset(),
               actual.getEndOffset());
      }
      if (expected.getType() == WILDCARD_TYPE) {
         return;
      }

      assertEquals(
            "Type not equals, got " + NodeTypes.getTypeName(actual.getType())
                  + " but was " + NodeTypes.getTypeName(expected.getType()),
            expected.getType(), actual.getType());
      assertEquals("Number of children not equals", expected.getChildren()
            .size(), actual.getChildren().size());

      if (Nodes.isString(expected)) {
         assertEquals("String content not equals",
               ((IStringNode) expected).getString(),
               ((IStringNode) actual).getString());
      }
      else if (Nodes.isKeyword(expected)) {
         assertEquals("Keyword instance not equal",
               ((IKeywordNode) expected).getKeywordInstance(),
               ((IKeywordNode) actual).getKeywordInstance());
         assertEquals("Keyword not equal",
               ((IKeywordNode) expected).getKeyword(),
               ((IKeywordNode) actual).getKeyword());
      }

      for (int i = 0; i < expected.getChildren().size(); i++) {
         compareIASTNode(expected.getChildren().get(i), actual.getChildren()
               .get(i), checkOffsets);
      }
   }

}
