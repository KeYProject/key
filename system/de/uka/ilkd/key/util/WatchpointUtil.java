package de.uka.ilkd.key.util;

import java.util.LinkedList;

import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.ListOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

public class WatchpointUtil {
    
 public static LinkedList<Node> getAllLeaveNodes(ETNode proofnodes){
   
     LinkedList<Node> leaves = new LinkedList<Node>();
     System.out.println("getting the leavenodes...");
     Node[] nodes = proofnodes.getProofTreeNodes().toArray();
     System.out.println("Arraysize: " + nodes.length);
     for (Node currentnode : nodes) {
        if(currentnode.leaf()){
          
            leaves.add(currentnode);
        }
     }System.out.println("size of leaves: " + leaves.size());
     return leaves;
     
 }
    

}
