package de.uka.ilkd.key.proof.delayedcut;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class DelayedCut {
        public static final int FORMULA_ON_LEFT_SIDE = 0;
        public static final int FORMULA_ON_RIGHT_SIDE = 1;
    
        private final Proof proof;
        private final Node  node;
        private final Node [] subtrees;
        private final int   cutMode;
        private final Term formula;
       
        
        public DelayedCut(Proof proof, Node node, Term formula, Node [] subtrees,
                int sideOfFormula) {
            super();
            assert sideOfFormula == FORMULA_ON_LEFT_SIDE || sideOfFormula == FORMULA_ON_RIGHT_SIDE;
            this.proof = proof;
            this.node = node;
            this.formula = formula;
            this.subtrees = subtrees;
            this.cutMode = sideOfFormula;
        }
        
        public Term getFormula() {
            return formula;
        }
        
        public Services getServices(){
            return proof.getServices();
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
        
        public int getCutMode() {
            return cutMode;
        }
        

    
        
    

}
