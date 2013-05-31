// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustification;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * This profile sets up KeY for verification of JavaCard programs.
 *
 */
public class JavaProfile extends AbstractProfile {

    private final static StrategyFactory DEFAULT =
        new JavaCardDLStrategy.Factory();

    private final static StrategyFactory SYMBOLIC_EXECUTION_FACTORY = new SymbolicExecutionStrategy.Factory();

    protected JavaProfile(String standardRules, ImmutableSet<GoalChooserBuilder> gcb) {
        super(standardRules, gcb);
     }

    protected JavaProfile(String standardRules) {
        super(standardRules);
     }

    public JavaProfile() {
        this("standardRules.key");
    }

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
        set = set.add(DEFAULT);
        set = set.add(SYMBOLIC_EXECUTION_FACTORY);
        return set;
    }

    
    protected ImmutableList<BuiltInRule> initBuiltInRules() {       
        ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules();
        
        builtInRules = builtInRules.prepend(WhileInvariantRule.INSTANCE)
                                   .prepend(BlockContractRule.INSTANCE)
                                   .prepend(UseDependencyContractRule.INSTANCE)
                                   .prepend(getInitialOneStepSimpilifier())
        			   //.prepend(PullOutConditionalsRule.INSTANCE)  // rule at the moment unsound
        			   .prepend(QueryExpand.INSTANCE);
  
        //contract insertion rule, ATTENTION: ProofMgt relies on the fact 
        // that Contract insertion rule is the FIRST element of this list!
        builtInRules = builtInRules.prepend(UseOperationContractRule.INSTANCE);

        return builtInRules;
    }
    
    /**
     * <p>
     * Returns the {@link OneStepSimplifier} instance which should be used
     * in this {@link JavaProfile}. It is added to the build in rules via
     * {@link #initBuiltInRules()}.
     * </p>
     * <p>
     * Sub profiles may exchange the {@link OneStepSimplifier} instance,
     * for instance for site proofs used in the symbolic execution tree extraction.
     * </p> 
     * @return The {@link OneStepSimplifier} instance to use.
     */
    protected OneStepSimplifier getInitialOneStepSimpilifier() {
       return OneStepSimplifier.INSTANCE;
    }

    /**
     * determines the justification of rule <code>r</code>. For a method contract rule it
     * returns a new instance of a {@link ComplexRuleJustification} otherwise the rule
     * justification determined by the super class is returned
     *
     * @return justification for the given rule
     */
    public RuleJustification getJustification(Rule r) {
        return r == UseOperationContractRule.INSTANCE 
               || r == UseDependencyContractRule.INSTANCE
               ? new ComplexRuleJustificationBySpec()
               : super.getJustification(r);
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
