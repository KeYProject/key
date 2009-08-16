package visualdebugger;

import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchpointUtil;

public class WatchpointUtilTest {

    private static ETNode etNode = null;
    /**
     * @param args
     */
    public static void main(String[] args) {

        
        try {
        ETNode etn = init();
        System.out.println("This ET has "+getETasList(etn).size() +" nodes.");
        WatchpointUtil.getAllLeafETNodes(etn);
        final ImmutableList<Node> proofTreeNodes = getNode().getProofTreeNodes();
	Node[] array = proofTreeNodes.toArray(new Node[proofTreeNodes.size()]);

        System.out.println("Array.length: " + array.length);
        WatchpointUtil.getLeafNodesInETNode(array);
        System.out.println("\nNormal Termination");
        System.exit(0); }
        catch (RuntimeException e){
            e.printStackTrace();
            System.out.println("\nAn error occured!");
            System.exit(-1);
        }
    }

    private static ETNode init() {

        Proof proof = new Proof(new Services());
        
        ETNode root = new ETNode(null, null);
        ETNode node1 = new ETNode(null, root);
        ETNode node2 = new ETNode(null, root);
        ETNode node3 = new ETNode(null, node1);
        ETNode node4 = new ETNode(null, node3);
        ETNode node5 = new ETNode(null, node3);

        root.addChild(node1);
        root.addChild(node2);
        node1.addChild(node3);
        node3.addChild(node4);
        node3.addChild(node5);
        
        Node n = new Node(proof, null, null, null, null);
        Node n1 = new Node(proof, null, null, n, null);
        Node n2 = new Node(proof, null, null, n, null);
        Node n3 = new Node(proof, null, null, n1, null);
        Node n4 = new Node(proof, null, null, n3, null);
        Node n5 = new Node(proof, null, null, n3, null);
        Node n6 = new Node(proof, null, null, n3, null);
        Node n7 = new Node(proof, null, null, n4, null);
        Node n8 = new Node(proof, null, null, n7, null);
        Node n9 = new Node(proof, null, null, n7, null);
        Node n10 = new Node(proof, null, null, n8, null);
        Node n11 = new Node(proof, null, null, n, null);
        
        n.add(n1);
        n.add(n2);
        n1.add(n3);
        n3.add(n4);
        n3.add(n5);
        n3.add(n6);
        n4.add(n7);
        n7.add(n8);
        n7.add(n9);
        n8.add(n10);
        
        ITNode itnode = new ITNode(n);
        ITNode itnode1 = new ITNode(n1);
        ITNode itnode2 = new ITNode(n2);
        ITNode itnode3 = new ITNode(n3);
        ITNode itnode4 = new ITNode(n4);
        ITNode itnode5 = new ITNode(n5);
        ITNode itnode6 = new ITNode(n6);
        ITNode itnode7 = new ITNode(n7);
        ITNode itnode8 = new ITNode(n8);
        ITNode itnode9 = new ITNode(n9);
        ITNode itnode10 = new ITNode(n10);
        ITNode itnode11 = new ITNode(n11);
        
        itnode.addChild(itnode1);
        itnode.addChild(itnode2);
        itnode1.addChild(itnode3);
        itnode3.addChild(itnode4);
        itnode3.addChild(itnode5);
        itnode3.addChild(itnode6);
        itnode4.addChild(itnode7);
        itnode7.addChild(itnode8);
        itnode7.addChild(itnode9);
        itnode8.addChild(itnode10);

        LinkedList<ITNode> itNodes = new LinkedList<ITNode>();
        itNodes.add(itnode4);
        itNodes.add(itnode5);
        itNodes.add(itnode7);
        itNodes.add(itnode8);
        itNodes.add(itnode9);

        root.addITNode(itnode);
        node1.addITNode(itnode1);
        node2.addITNode(itnode2);
        node2.addITNode(itnode11);
        node3.addITNode(itnode3);
        node4.addITNodes(itNodes);
        node5.addITNode(itnode5);
        
        setNode(node4);
        return root;
    }

    private static void setNode(ETNode etn) {
        etNode = etn;
    }

    private static ETNode getNode() {
        return etNode;
    }
    /**
     * Gets the executiontree as list.
     * 
     * @param etn the ETNode containing the current ET
     * 
     * @return the executiontree as list
     */
    public static LinkedList<ETNode> getETasList(ETNode etn) {
        
        LinkedList<ETNode> executionTree = new LinkedList<ETNode>();
        executionTree.add(etn);
        LinkedList<ETNode> children = etn.getChildrenList();

            for (ETNode node : children) {
                executionTree.addAll(getETasList(node));
            }
        return executionTree;
    }
}
