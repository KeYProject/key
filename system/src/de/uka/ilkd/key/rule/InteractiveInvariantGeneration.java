package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

public class InteractiveInvariantGeneration implements Rule, BuiltInRule {

        public static InteractiveInvariantGeneration INSTANCE = new InteractiveInvariantGeneration();
        
        private String name = "Loop Invariant - interactive";
        private String displayName = "LI";
        
        private InteractiveInvariantGeneration() {
        }
        
        @Override
        public ImmutableList<Goal> apply(Goal goal, Services services,
                        RuleApp ruleApp) {
                /*
                 *getLoopInvariant  
                 */
                
                
                return WhileInvariantRule.INSTANCE.apply(goal, services, ruleApp);
        }

        @Override
        public String displayName() {

                return displayName;
        }

        @Override
        public Name name() {

                return name();
        }

        @Override
        public boolean isApplicable(Goal goal, PosInOccurrence pio) {
                
                //1. Auto Mode? => NO
                if (!Main.getInstance().mediator().autoMode()) {
                        return false;
                } else {
                        if (true) {
                                
                        }
                }
                return false;
        }

}
