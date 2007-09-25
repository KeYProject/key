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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.*;


/**
 * Strategy tailored to VBT aimed symbolic execution.
 */
public class VBTStrategy extends JavaCardDLStrategy {

    protected  static StrategyProperties setupStrategyProperties() {
        final StrategyProperties res = new StrategyProperties ();
        res.setProperty ( StrategyProperties.LOOP_OPTIONS_KEY,
                          StrategyProperties.LOOP_EXPAND );
        res.setProperty ( StrategyProperties.METHOD_OPTIONS_KEY,
                          StrategyProperties.METHOD_EXPAND );
        res.setProperty ( StrategyProperties.QUERY_OPTIONS_KEY,
                          StrategyProperties.QUERY_NONE );
        res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, 
                        StrategyProperties.QUANTIFIERS_INSTANTIATE);
        return res;
    }
    
    protected VBTStrategy(Proof p_proof) {
        
        super ( p_proof, setupStrategyProperties () );

        clearRuleSetBindings ( getCostComputationDispatcher (), "test_gen" );
        bindRuleSet ( getCostComputationDispatcher (), "test_gen",
                      add ( longConst ( -1000 ),
			    NonDuplicateAppModPositionFeature.INSTANCE));
        clearRuleSetBindings ( getCostComputationDispatcher (), "split_cond" );
        bindRuleSet ( getCostComputationDispatcher (), "split_cond", -1000);
        clearRuleSetBindings ( getCostComputationDispatcher (), "split" );
        bindRuleSet ( getCostComputationDispatcher (), "split", -1000);

        clearRuleSetBindings ( getCostComputationDispatcher (), "beta" );
        bindRuleSet ( getCostComputationDispatcher (), "beta", -1000);
    
        clearRuleSetBindings ( getCostComputationDispatcher (), "inReachableStateImplication" );
        bindRuleSet ( getCostComputationDispatcher (), "inReachableStateImplication",
                inftyConst () );
        clearRuleSetBindings ( getCostComputationDispatcher (), "cut_direct" );
        bindRuleSet ( getCostComputationDispatcher (), "cut_direct",
		      inftyConst ());
        clearRuleSetBindings ( getCostComputationDispatcher (), "simplify_prog" );
        bindRuleSet ( getCostComputationDispatcher (), "simplify_prog",
		      10000);
        clearRuleSetBindings ( getCostComputationDispatcher (), "simplify_prog_subset" );
        bindRuleSet ( getCostComputationDispatcher (), "simplify_prog_subset",
		      10000);
    }

    

    
    
    public Name name () {
        return new Name("VBTStrategy");
    }

    public static class Factory extends StrategyFactory {

        public Factory () {
	}

        public Strategy create ( Proof p_proof, 
                StrategyProperties strategyProperties ) {
            return new VBTStrategy ( p_proof);
        }
        
        public Name name () {
            return new Name("VBTStrategy");
        }
    }
}
