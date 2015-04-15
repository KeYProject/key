package org.key_project.jmlediting.core.test.utilities;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class ASTTestUtils {

   public static final int T0 = NodeTypes.getNewType("0");
   public static final int T1 = NodeTypes.getNewType("1");
   public static final int T2 = NodeTypes.getNewType("2");
   public static final int T3 = NodeTypes.getNewType("3");
   public static final int T4 = NodeTypes.getNewType("4");
   public static final int T5 = NodeTypes.getNewType("5");
   public static final int T6 = NodeTypes.getNewType("6");

   public static final IASTNode NODE_1 = Nodes.createNode(
         0,
         40,
         T0,
         Nodes.createNode(10, 20, T1, Nodes.createNode(10, 15, T3),
               Nodes.createNode(15, 19, T4, Nodes.createNode(18, 19, T5))),
               Nodes.createNode(25, 40, T2, Nodes.createNode(25, 40, T6)));

   public static final IASTNode NODE_2 = Nodes.createNode(0, 0, T0);

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
