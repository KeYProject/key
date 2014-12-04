package org.key_project.jmlediting.core.test.dom;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class ASTTestUtils {

   public static final IASTNode NODE_1 = Nodes.createNode(
         0,
         40,
         0,
         Nodes.createNode(10, 20, 1, Nodes.createNode(10, 15, 3),
               Nodes.createNode(15, 19, 4, Nodes.createNode(18, 18, 5))),
         Nodes.createNode(25, 40, 2, Nodes.createNode(25, 40, 6)));

   public static final IASTNode NODE_2 = Nodes.createNode(0, 0, 10);

   public static final IASTNode NODE_3 = Nodes
         .createNode(
               0,
               20,
               NodeTypes.NODE,
               Nodes.createString(0, 5, "1"),
               Nodes.createString(6, 10, "2"),
               Nodes.createString(11, 15, "3"),
               Nodes.createNode(16, 20, NodeTypes.NODE,
                     Nodes.createString(16, 17, "4"),
                     Nodes.createString(18, 19, "5"),
                     Nodes.createString(20, 20, "6")));

}
