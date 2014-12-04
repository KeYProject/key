package org.key_project.jmlediting.core.test.dom;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import java.util.List;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.Nodes;

public class ASTSearchTest {

   @Test
   public void testSearchForASTWithPosition() {
      final IASTNode mainNode = ASTTestUtils.NODE_1;
      assertNull("Search outside left returns not null",
            Nodes.getDepthMostNodeWithPosition(-5, mainNode));
      assertNull("Search outside right returns not null",
            Nodes.getDepthMostNodeWithPosition(45, mainNode));
      assertEquals(0, Nodes.getDepthMostNodeWithPosition(22, mainNode)
            .getType());
      assertEquals(1, Nodes.getDepthMostNodeWithPosition(20, mainNode)
            .getType());
      assertEquals(3, Nodes.getDepthMostNodeWithPosition(10, mainNode)
            .getType());
      assertEquals(3, Nodes.getDepthMostNodeWithPosition(14, mainNode)
            .getType());
      assertEquals(4, Nodes.getDepthMostNodeWithPosition(17, mainNode)
            .getType());
      assertEquals(5, Nodes.getDepthMostNodeWithPosition(18, mainNode)
            .getType());
      assertEquals(6, Nodes.getDepthMostNodeWithPosition(30, mainNode)
            .getType());
   }

   @Test
   public void testFindNothing() {
      final Object result = ASTTestUtils.NODE_3
            .serach(new INodeSearcher<Object>() {

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
