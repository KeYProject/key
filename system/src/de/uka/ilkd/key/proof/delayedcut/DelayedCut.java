package de.uka.ilkd.key.proof.delayedcut;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;

public class DelayedCut {
        public static final int DECISION_PREDICATE_IN_ANTECEDENT = 0;
        public static final int DECISION_PREDICATE_IN_SUCCEDENT = 1;
    
        private final Proof proof;
        private final Node  node;
        private final Node [] subtrees;
        private final int   cutMode;
        private final Term decisionPredicate;
        private final RuleApp firstAppliedRuleApp;
        private NoPosTacletApp hideApp = null;
        
       
        
        public DelayedCut(Proof proof, Node node, Term formula, Node [] subtrees,
                int sideOfDecisionPredicate, RuleApp firstAppliedRuleApp) {
            super();
            assert sideOfDecisionPredicate == DECISION_PREDICATE_IN_ANTECEDENT || sideOfDecisionPredicate == DECISION_PREDICATE_IN_SUCCEDENT;
            this.proof = proof;
            this.node = node;
            this.decisionPredicate = formula;
            this.subtrees = subtrees;
            this.cutMode = sideOfDecisionPredicate;
            this.firstAppliedRuleApp = firstAppliedRuleApp;

        }
        
        public Term getFormula() {
            return decisionPredicate;
        }
        
        public RuleApp getFirstAppliedRuleApp() {
            return firstAppliedRuleApp;
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
        
        public void setHideApp(NoPosTacletApp hideApp) {
            if(this.hideApp != null){
                throw new IllegalArgumentException("There already exists an app.");
            }
            this.hideApp = hideApp;
        }
        
        public NoPosTacletApp getHideApp() {
            return hideApp;
        }
        
        public Node[] getSubtrees() {
            return subtrees;
        }
        
        public int getCutMode() {
            return cutMode;
        }
        
        public boolean isDecisionPredicateInAntecendet(){
            return cutMode == DECISION_PREDICATE_IN_ANTECEDENT;
        }
        

    
        
    

}
