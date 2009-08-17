// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustification;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;

/**
 * This profile sets up KeY for verification of JavaCard programs.
 *
 */
public class JavaProfile extends AbstractProfile {

    private final static StrategyFactory DEFAULT =
        new JavaCardDLStrategy.Factory();


    protected JavaProfile(String standardRules, ImmutableSet<GoalChooserBuilder> gcb,
            IMain main) {
        super(standardRules, gcb, main);
     }

    protected JavaProfile(String standardRules, IMain main) {
        super(standardRules, main);
     }

    public JavaProfile() {
        this("standardRules.key", null);
    }

    public JavaProfile(IMain main) {
        this("standardRules.key", main);
    }

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
        set = set.add(DEFAULT);
        return set;
    }

    protected UseOperationContractRule getContractRule() {
        return UseOperationContractRule.INSTANCE;
    }
    
    
    protected ImmutableList<BuiltInRule> initBuiltInRules() {       
        ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules();
        
        builtInRules = builtInRules.prepend(WhileInvariantRule.INSTANCE)
                                   .prepend(OneStepSimplifier.INSTANCE);
  
        //contract insertion rule, ATTENTION: ProofMgt relies on the fact 
        // that Contract insertion rule is the FIRST element of this list!
        builtInRules = builtInRules.prepend(getContractRule());

        return builtInRules;
    }

    /**
     * determines the justification of rule <code>r</code>. For a method contract rule it
     * returns a new instance of a {@link ComplexRuleJustification} otherwise the rule
     * justification determined by the super class is returned
     *
     * @return justification for the given rule
     */
    public RuleJustification getJustification(Rule r) {
        return r == getContractRule() ? new ComplexRuleJustificationBySpec() :
            super.getJustification(r);
    }


    /**
     * the name of the profile
     */
    public String name() {
        return "Java Profile";
    }

    /**
     * the default strategy factory to be used
     */
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }
}
