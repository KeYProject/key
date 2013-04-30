 
package de.uka.ilkd.key.gui.macros;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.logic.op.UpdateApplication;

public class SimplifyHeap extends StrategyProofMacro{
    private static final String[] ADMITTED_RULES = {
//        "orRight", "impRight", "close",
//        "sequentialToParallel1", "sequentialToParallel2", "sequentialToParallel3",
//        "simplifyUpdate1","simplifyUpdate2","simplifyUpdate3",
    };
    
    //most rules also applied by one step simplifier
    private static final String[] UPD_SIMPLIFICATION_RULES = { 
    	 "applyOnSkip","applyOnRigidTerm","applyOnElementary","applyOnRigidFormula",
    	"applyOnParallel","applyOnPV","parallelWithSkip1","parallelWithSkip2","applySkip1","applySkip2","applySkip3",
    	"simplifyIfThenElseUpdate1","simplifyIfThenElseUpdate2","simplifyIfThenElseUpdate3","simplifyIfThenElseUpdate4",
	"selectOfAnon", "selectOfAnonEQ", "selectOfStore", "elementOfUnion", "elementOfSingleton", "elementOfFreshLocs", 
	"sortsDisjointModuloNull", "selectOfMemset", "elementOfArrayRange", "selectOfCreate"
};
    private static final String[] PERMITTED_SIMPLIFICATION_RULES ={ 
	  "ifthenelse_false", "ifthenelse_true", 
	   //"replace_known_right", "replace_known_left",
	  "concrete_and_1", "concrete_and_2", "concrete_and_3", "concrete_and_4", "concrete_or_1", "concrete_or_2", "concrete_or_3", "concrete_or_4", 
	  "equalUnique", "eqClose", "equal_literals", "close",
//	  "sequentialToParallel1", "sequentialToParallel2", "sequentialToParallel3",
//          "simplifyUpdate1","simplifyUpdate2","simplifyUpdate3",
	  "concrete_not_1", "concrete_not_2", "true_left", "false_right"};
    private static final Set<String> PERMITTED_RULE_SET = asSet(PERMITTED_SIMPLIFICATION_RULES);
    //private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);
    private static final Set<String> ADMITTED_RULES_SET = asSet(PERMITTED_SIMPLIFICATION_RULES);
	
    private static final Set<String> SIMPLIFIER_COPY_RULE_SET = asSet(UPD_SIMPLIFICATION_RULES);
    
    private static final Name SYMBOLIC_EXECUTION_RULESET = new Name("symbEx");
    
	@Override
	public String getName() {
		return "SimplifyHeap";
	}

	@Override
	public String getDescription() {
		return "<html><ol><li>Simplify heap expressions in formulas</ol>";
	}


	
    /*
     * convert a string array to a set of strings
     */
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new HashSet<String>(Arrays.asList(strings)));
    }

    /*
     * find a modality term in a node
     */
    private static boolean hasModality(Node node) {
        Sequent sequent = node.sequent();
        for (SequentFormula sequentFormula : sequent) {
            if(hasModality(sequentFormula.formula())) {
                return true;
            }
        }

        return false;
    }

    /*
     * recursively descent into the term to detect a modality.
     */
    private static boolean hasModality(Term term) {
        /*if(term.op() instanceof Modality) {
            return true;
        }

        for (Term sub : term.subs()) {
            if(hasModality(sub)) {
                return true;
            }
        }*/

        return true;
    }

    /*
     * Checks if a rule is marked as not suited for interaction.
     */
    private static boolean isSymbExTagged(Rule rule, Services services) {
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            ImmutableList<RuleSet> ruleSets = taclet.getRuleSets();
            RuleSet interactionRuleSet = (RuleSet)services.getNamespaces().ruleSets().
                    lookup(SYMBOLIC_EXECUTION_RULESET);
            return ruleSets.contains(interactionRuleSet);
        }
        return false;
    }

    private static class SimplifyHeapStrategy implements Strategy {
        private static final Name NAME = new Name("Simplify heap strategy");
        private final KeYMediator mediator;
        private final PosInOccurrence posInOcc;
        private final Strategy delegate;

        public SimplifyHeapStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
            this.mediator = mediator;
            this.posInOcc = posInOcc;
            this.delegate = mediator.getInteractiveProver().getProof().getActiveStrategy();
        }
        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
            Rule rule = app.rule();

            String name = rule.name().toString();
            /**
             * only rules containing symbEx as heuristic should be applied 
             */

	    if(rule == OneStepSimplifier.INSTANCE){
	      return delegate.computeCost(app, pio, goal);
	    } 

            //if(hasModality(goal.node())) {

               /* if(name.startsWith("Use Operation Contract") ||
                        name.startsWith("Loop Invariant") ||
                        ADMITTED_RULES_SET.contains(name) ||
                        isSymbExTagged(rule, goal.proof().getServices())) {

                    return delegate.computeCost(app, pio, goal);
                }*/ 

                if(SIMPLIFIER_COPY_RULE_SET.contains(name)) {
//                    PosInTerm pit = pio.posInTerm();
//                    Term curTerm = pio.constrainedFormula().formula();
//                    IntIterator it = pit.iterator();
//                    while(it.hasNext()) {
//                        int curIdx = it.next();
//                        if(curTerm.op() == UpdateApplication.UPDATE_APPLICATION && curIdx == 0) {
                            RuleAppCost rac = delegate.computeCost(app, pio, goal);
			    return rac;
//                        }
//                    }

                }

           //     if(name.equals("andRight") && hasModality(pio.subTerm())) {
           //         return delegate.computeCost(app, pio, goal);
           //     }

            //    return TopRuleAppCost.INSTANCE;
            //}

            if(ADMITTED_RULES_SET.contains(name)) {
//System.out.println("Checked admitted rule: " + name);
                return LongRuleAppCost.ZERO_COST;
            }


	   if (name.startsWith("replace_known_right") && (pio.isInAntec() || !pio.isTopLevel())) {
  
	      boolean isBehindUpdate = false;
	      PosInOccurrence tempPio = pio;
	      while(!tempPio.isTopLevel()) {
		  tempPio = tempPio.up();
		  if (tempPio.subTerm().op() == UpdateApplication.UPDATE_APPLICATION) {
		    isBehindUpdate = true;
		  }
	      }

	      if (isBehindUpdate) {
		return TopRuleAppCost.INSTANCE;
	      } else {
		return LongRuleAppCost.ZERO_COST;
	      }
	   }
                
           if (name.startsWith("replace_known_left") && (!pio.isInAntec() || !pio.isTopLevel())) {
	      boolean isBehindUpdate = false;
	      PosInOccurrence tempPio = pio;
		while(!tempPio.isTopLevel()) {
		  tempPio = tempPio.up();
		  if (tempPio.subTerm().op() == UpdateApplication.UPDATE_APPLICATION) {
		    isBehindUpdate = true;
		  }
	      }

	      if (isBehindUpdate) {
		return TopRuleAppCost.INSTANCE;
	      } else {
		return LongRuleAppCost.ZERO_COST;
	      }
	    }

           // if(name.startsWith("Class_invariant_axiom_for")) {
           //     return LongRuleAppCost.ZERO_COST;
           // }

            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return computeCost(app, pio, goal) != TopRuleAppCost.INSTANCE;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

    }
	@Override
	protected Strategy createStrategy(KeYMediator mediator,
			PosInOccurrence posInOcc) {
		return new SimplifyHeapStrategy(mediator,posInOcc);
	}

}
