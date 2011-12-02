package de.uka.ilkd.key.proof.join;

import java.util.Comparator;
import java.util.TreeSet;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

public class ProspectivePartner {
        private final Term[] updates = new Term[2];
        private final Term   commonFormula;
        private final Node[] nodes = new Node[2];
        private final PosInOccurrence [] positions = new PosInOccurrence[2];
        private Node commonnParent = null;
        private Term commonPredicate = null; 
        private boolean checkedForCommonPredicate = false;
        
        
        public ProspectivePartner(Term commonFormula,Node node1, Term update1, PosInOccurrence pos1,
                Node node2, Term update2, PosInOccurrence pos2) {
            super();
            this.commonFormula = commonFormula;
            updates[0] = update1;
            updates[1] = update2;
            nodes[0]   = node1;
            nodes[1]   = node2;
            positions[0] = pos1;
            positions[1] = pos2;
        }
        
        public Term getCommonFormula() {
            return commonFormula;
        }
        
        public Node getNode(int index){
            return nodes[index];
        }
        
        public Term getUpdate(int index){
            return updates[index];
        }
        
        public PosInOccurrence getPosition(int index){
            return positions[index];
        }
        
        
        public Term getCommonPredicate(){
            if(!checkedForCommonPredicate){
                checkedForCommonPredicate = true;
               String branchLabel = getCommonParent().child(0).getNodeInfo().getBranchLabel();
               if(branchLabel != null && (branchLabel.endsWith("TRUE") || branchLabel.endsWith("FALSE") )){
                   String suffix = branchLabel.endsWith("TRUE") ? "TRUE" : "FALSE";
                   int index = branchLabel.lastIndexOf(suffix);
                   branchLabel = branchLabel.substring(0, index);
                   System.out.println(branchLabel);
               }
            }
            return commonPredicate;
        }
        
        
        public Node getCommonParent(){
            if(commonnParent == null){
                TreeSet<Node> set = new TreeSet<Node>(new Comparator<Node>() {

                    @Override
                    public int compare(Node o1, Node o2) {
                        
                        return o1.serialNr()-o2.serialNr();
                    }
                });
            

                Node node = nodes[0];
                while(!node.root()){
                    set.add(node);
                    node = node.parent();
                }
                
                node = nodes[1];
                while(node.parent() != null && !set.contains(node)){
                    node = node.parent();
                }
                
                if(set.contains(node)){
                    commonnParent = node;
                }                
            }      
            
            return commonnParent;
        }
        
        
        
        
        

}
