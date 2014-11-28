package org.key_project.jmlediting.core.dom;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import org.junit.Test;

public class ASTSearchTest {

   @Test
   public void testSearchForASTWithPosition() {
      IASTNode mainNode = Nodes.createNode(
            0,
            40,
            0,
            Nodes.createNode(10, 20, 1, Nodes.createNode(10, 15, 3),
                  Nodes.createNode(15, 19, 4, Nodes.createNode(18, 18, 5))),
            Nodes.createNode(25, 40, 2, Nodes.createNode(25, 40, 6)));
      assertNull("Search outside left returns not null", Nodes.getDepthMostNodeWithPosition(-5, mainNode));
      assertNull("Search outside right returns not null", Nodes.getDepthMostNodeWithPosition(45, mainNode));
      assertEquals(0, Nodes.getDepthMostNodeWithPosition(22, mainNode).getType());
      assertEquals(1, Nodes.getDepthMostNodeWithPosition(20, mainNode).getType());
      assertEquals(3, Nodes.getDepthMostNodeWithPosition(10, mainNode).getType());
      assertEquals(3, Nodes.getDepthMostNodeWithPosition(14, mainNode).getType());
      assertEquals(4, Nodes.getDepthMostNodeWithPosition(17, mainNode).getType());
      assertEquals(5, Nodes.getDepthMostNodeWithPosition(18, mainNode).getType());
      assertEquals(6, Nodes.getDepthMostNodeWithPosition(30, mainNode).getType());
   }
}
