// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.delayedcut;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.ExperimentalFeature;

/**
 * This class wraps the information about the delayed cut. It only wraps data but not functional 
 * information. 
 */
public class DelayedCut {
        public static final int DECISION_PREDICATE_IN_ANTECEDENT = 0;
        public static final int DECISION_PREDICATE_IN_SUCCEDENT = 1;
        
        /** Controls whether delayed cut is available to the user.
         * WARNING: You may refresh your GUI elements after (de-)activation.
         */
        public static final ExperimentalFeature FEATURE = new ExperimentalFeature(){
            private boolean active = true;

            @Override
            public void deactivate() {
                de.uka.ilkd.key.gui.join.JoinMenuItem.FEATURE.deactivate();
                active = false;
            }
            
            @Override
            public void activate() { active = true; }
            
            @Override
            public boolean active() { return active; }
        };
            
        private final Proof proof;
        private final Node  node;
        private final ImmutableList<Node>  subtrees;
        private final int   cutMode;
        private final Term decisionPredicate;
        private final RuleApp firstAppliedRuleApp;
        private NoPosTacletApp hideApp = null;
        private ImmutableList<NodeGoalPair> goalsAfterUncovering = null;
        private Goal                remainingGoal = null;
        
       
        
        public DelayedCut(Proof proof, Node node, Term formula, ImmutableList<Node>  subtrees,
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
        
        void setHideApp(NoPosTacletApp hideApp) {
            if(this.hideApp != null){
                throw new IllegalArgumentException("There already exists an app.");
            }
            this.hideApp = hideApp;
        }
        
        void setGoalsAfterUncovering(
                ImmutableList<NodeGoalPair> goalsAfterUncovering) {
            if(this.goalsAfterUncovering != null){
                throw new IllegalArgumentException("There already exists a list of goals.");
            }
            this.goalsAfterUncovering = goalsAfterUncovering;
        }
        
        void setRemainingGoal(Goal remainingGoal) {
            this.remainingGoal = remainingGoal;
        }
        
        public Goal getRemainingGoal() {
            return remainingGoal;
        }
        
        public ImmutableList<NodeGoalPair> getGoalsAfterUncovering() {
            return goalsAfterUncovering;
        }
        
        public NoPosTacletApp getHideApp() {
            return hideApp;
        }
        
        public ImmutableList<Node> getSubtrees() {
            return subtrees;
        }
        
        public int getCutMode() {
            return cutMode;
        }
        
        public boolean isDecisionPredicateInAntecendet(){
            return cutMode == DECISION_PREDICATE_IN_ANTECEDENT;
        } 
    

}