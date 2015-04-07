package org.key_project.jmlediting.core.test.dom;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.key_project.jmlediting.core.test.utilities.ASTTestUtils.*;

import java.util.List;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.test.utilities.ASTTestUtils;

public class ASTSearchTest {

   @Test
   public void testSearchForASTWithPosition() {
      final IASTNode mainNode = ASTTestUtils.NODE_1;
      assertNull("Search outside left returns not null",
            Nodes.getDepthMostNodeWithPosition(-5, mainNode));
      assertNull("Search outside right returns not null",
            Nodes.getDepthMostNodeWithPosition(45, mainNode));
      assertEquals(T0, Nodes.getDepthMostNodeWithPosition(22, mainNode)
            .getType());
      assertEquals(T1, Nodes.getDepthMostNodeWithPosition(19, mainNode)
            .getType());
      assertEquals(T3, Nodes.getDepthMostNodeWithPosition(10, mainNode)
            .getType());
      assertEquals(T3, Nodes.getDepthMostNodeWithPosition(13, mainNode)
            .getType());
      assertEquals(T4, Nodes.getDepthMostNodeWithPosition(16, mainNode)
            .getType());
      assertEquals(T5, Nodes.getDepthMostNodeWithPosition(18, mainNode)
            .getType());
      assertEquals(T6, Nodes.getDepthMostNodeWithPosition(29, mainNode)
            .getType());
   }

   @Test
   public void testFindNothing() {
      final Object result = ASTTestUtils.NODE_3
            .search(new INodeSearcher<Object>() {

               @Override
               public Object searchNode(final IASTNode node) {
                  return null;
               }

               @Override
               public IASTNode selectChild(final List<IASTNode> children) {
                  return children.get(children.size() - 1);
               }
            });
      assertNull("Search does not return null", result);
   }
}
