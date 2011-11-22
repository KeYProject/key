package de.uka.ilkd.key.proof.delayedcut;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class DelayedCut {
        private final Proof proof;
        private final Node  node;
        private final Term  formula;
        private final Node [] subtrees;
        
        public DelayedCut(Proof proof, Node node, Term formula, Node [] subtrees) {
            super();
            this.proof = proof;
            this.node = node;
            this.formula = formula;
            this.subtrees = subtrees;
        }
        
        public Term getFormula() {
            return formula;
        }
        
        public Node getNode() {
            return node;
        }
        
        public Proof getProof() {
            return proof;
        }
        
        public Node[] getSubtrees() {
            return subtrees;
        }
    
        
    

}
