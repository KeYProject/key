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
import de.uka.ilkd.key.strategy.feature.BreakpointFeature;
import de.uka.ilkd.key.strategy.feature.InUpdateFeature;
import de.uka.ilkd.key.strategy.feature.LabelFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

/**
 * Strategy tailored to VBT aimed symbolic execution.
 */
public class DebuggerStrategy extends VBTStrategy {
    
    private ListOfNamed h;

   protected static StrategyProperties setupStrategyProperties() {
        final StrategyProperties res = new StrategyProperties();
        res.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                StrategyProperties.LOOP_EXPAND);
        res.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                StrategyProperties.METHOD_EXPAND);
        res.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_NONE);
        if (VisualDebugger.quan_splitting)
            res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_INSTANTIATE);
        else res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING);
        
        return res;
    }

   protected DebuggerStrategy(Proof p_proof) {
       super ( p_proof );
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
               ifZero(LabelFeature.create(),longConst(-200000),longConst(0)));

       bindRuleSet ( d, "beta",
               ifZero(LabelFeature.create(),longConst(-200000),longConst(0)));

       final NamespaceSet nss = p_proof.getNamespaces ();

       assert nss != null : "Rule set namespace not available.";               

       h= nss.ruleSets().allElements();

       IteratorOfNamed it =h.iterator();
       while (it.hasNext()){
           bindRuleSet ( d, it.next().name().toString(),                    
                   ifZero(InUpdateFeature.create(p_proof),inftyConst(),longConst(0)));
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
            return new DebuggerStrategy(p_proof);
        }

        public Name name() {
            return new Name("DebuggerStrategy");
        }
    }
}
