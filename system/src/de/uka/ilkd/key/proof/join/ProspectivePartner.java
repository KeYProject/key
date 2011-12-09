package de.uka.ilkd.key.proof.join;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

public class ProspectivePartner {
        private final Term[] updates = new Term[2];
        private final Term   commonFormula;
        private final Term[]   formula = new Term[2];
        private final Node[] nodes = new Node[2];
        private final PosInOccurrence [] positions = new PosInOccurrence[2];
        private Term commonPredicate = null; 
        private Node commonParent = null;

        
        
        public ProspectivePartner(Term commonFormula,Node node1,Term formula1, Term update1, PosInOccurrence pos1,
                Node node2,Term formula2, Term update2, PosInOccurrence pos2) {
            super();
            this.commonFormula = commonFormula;
            formula[0] = formula1;
            formula[1] = formula2;
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
        
        public void setCommonPredicate(Term commonPredicate) {
            this.commonPredicate = commonPredicate;
        }
        
        public Term getCommonPredicate() {
            return commonPredicate;
        }
        
        public void setCommonParent(Node commonParent) {
            this.commonParent = commonParent;
        }
        
        public Node getCommonParent() {
            return commonParent;
        }
        
        public Sequent getSequent(int index){
            return getNode(index).sequent();
        }
        
        public Term getFormula(int i){
            return formula[i];
        }

        
        
      
        
        
        
        

}
