// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

/**
 * Strategy tailored to VBT aimed symbolic execution.
 */
public class DebuggerStrategy extends VBTStrategy {
    
    public static final String VISUAL_DEBUGGER_SPLITTING_RULES_KEY = "VD_SPLITTING_RULES_KEY";
    public static final String VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY = 
        "VD_IN_UPDATE_AND_ASSUMES_RULES_KEY";
    public static final String VISUAL_DEBUGGER_IN_INIT_PHASE_KEY = "VD_IN_INIT_PHASE_KEY";

    public static final String VISUAL_DEBUGGER_TRUE= "TRUE";
    public static final String VISUAL_DEBUGGER_FALSE = "FALSE";


    private ListOfNamed h;

    public static StrategyProperties getDebuggerStrategyProperties(boolean splittingRulesAllowed,
            boolean inUpdateAndAssumes, boolean inInitPhase) {
        final StrategyProperties res = new StrategyProperties();
        res.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                StrategyProperties.LOOP_EXPAND);
        res.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                StrategyProperties.METHOD_EXPAND);
        res.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_NONE);
        if (VisualDebugger.quan_splitting) {
            res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                    StrategyProperties.QUANTIFIERS_INSTANTIATE);
        } else {
            res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, 
                StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        }
        
        res.setProperty(VISUAL_DEBUGGER_SPLITTING_RULES_KEY, 
                splittingRulesAllowed ? VISUAL_DEBUGGER_TRUE :
                    VISUAL_DEBUGGER_FALSE);

        res.setProperty(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY, 
                inUpdateAndAssumes ? VISUAL_DEBUGGER_TRUE :
                    VISUAL_DEBUGGER_FALSE);

        res.setProperty(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY, 
                inInitPhase ? VISUAL_DEBUGGER_TRUE :
                    VISUAL_DEBUGGER_FALSE);

        return res;
    }

   protected DebuggerStrategy(Proof p_proof, StrategyProperties props) {
       super ( p_proof, props );

       RuleSetDispatchFeature d = getCostComputationDispatcher();

       bindRuleSet(d, "simplify_autoname", ifZero(BreakpointFeature.create(),
               inftyConst(), longConst(0)));
       bindRuleSet(d, "method_expand", ifZero(BreakpointFeature.create(),
               inftyConst(), longConst(0)));   
       bindRuleSet(d, "debugger", inftyConst());
       bindRuleSet(d, "statement_sep", longConst(-200));

       bindRuleSet(d, "test_gen_empty_modality_hide", inftyConst());

       bindRuleSet(d, "test_gen_quan", inftyConst());

       bindRuleSet ( d, "instanceof_to_exists",  inftyConst());


       bindRuleSet ( d, "split_cond",
               ifZero(LabelFeature.INSTANCE,longConst(-200000),longConst(0)));

       bindRuleSet ( d, "beta",
               ifZero(LabelFeature.INSTANCE,longConst(-200000),longConst(0)));

       final NamespaceSet nss = p_proof.getNamespaces ();

       assert nss != null : "Rule set namespace not available.";               

       // FIXME: do not add it for each rule set add it as sum feature
       
       h = nss.ruleSets().allElements();

       final boolean isSplittingAllowed = props.
           get(VISUAL_DEBUGGER_SPLITTING_RULES_KEY).equals(VISUAL_DEBUGGER_TRUE);

       final boolean inUpdateAndAssumes = props.
          get(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY).equals(VISUAL_DEBUGGER_TRUE);

       final boolean inInitPhase = props.
          get(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY).equals(VISUAL_DEBUGGER_TRUE);
              
       final Feature inUpdateFeature = InUpdateFeature.create(isSplittingAllowed, 
               inUpdateAndAssumes, inInitPhase);
       
       final IteratorOfNamed it =h.iterator();
       while (it.hasNext()){
           bindRuleSet ( d, it.next().name().toString(),                    
                   ifZero(inUpdateFeature, inftyConst(),longConst(0)));
       }
   }

    public Name name() {
        return new Name("DebuggerStrategy");
    }

    public static class Factory extends StrategyFactory {

        public Factory() {
        }

        public Strategy create(Proof p_proof,
                StrategyProperties strategyProperties) {
            
            injectDebuggerDefaultOptionsIfUnset(strategyProperties);
            
            return new DebuggerStrategy(p_proof, strategyProperties);
        }

        private void injectDebuggerDefaultOptionsIfUnset(
                StrategyProperties props) {

            if (!props.containsKey(VISUAL_DEBUGGER_SPLITTING_RULES_KEY)) {
                props.put(VISUAL_DEBUGGER_SPLITTING_RULES_KEY, VISUAL_DEBUGGER_TRUE);
            }

            if (!props.containsKey(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY)) {
                props.put(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY, VISUAL_DEBUGGER_FALSE);
            }

            if (!props.containsKey(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY)) {
                props.put(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY, VISUAL_DEBUGGER_TRUE);
            }
        }

        public Name name() {
            return new Name("DebuggerStrategy");
        }
    }
}
