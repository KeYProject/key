package org.key_project.jmlediting.core.test.dom;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class ASTNodeTest {

   @Test(expected = IllegalArgumentException.class)
   public void createInvalidNodeOffset() {
      Nodes.createNode(10, 5, NodeTypes.NODE);
   }

   @Test(expected = IllegalArgumentException.class)
   public void createInvalidNodeUnregisteredType() {
      Nodes.createNode(0, 0, 342);
   }

   @Test(expected = IllegalArgumentException.class)
   public void createInvalidNodeChildrenOutOfRangeBegin() {
      final IASTNode child = Nodes.createNode(0, 10, NodeTypes.NODE);
      Nodes.createNode(5, 20, NodeTypes.NODE, child);
   }

   @Test(expected = IllegalArgumentException.class)
   public void createInvalidNodeChildrenOutOfRangeEnd() {
      final IASTNode child = Nodes.createNode(5, 15, NodeTypes.NODE);
      Nodes.createNode(0, 10, NodeTypes.NODE, child);
   }

}
