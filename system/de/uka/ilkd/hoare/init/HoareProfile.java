package de.uka.ilkd.hoare.init;

import de.uka.ilkd.hoare.rule.HoareLoopInvariantRule;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;
import de.uka.ilkd.key.rule.UpdateSimplificationRule;
import de.uka.ilkd.key.strategy.*;

/**
 * this profile sets up the KeY system to support the Hoare Update Logic
 * used in the Programmverification course in Chalmers
 */
public class HoareProfile extends AbstractProfile {

    private final static StrategyFactory DEFAULT = new HoareStrategy.Factory();
    
    /**
     * creates the profile for the Hoare with Updates logic     
     */
    public HoareProfile() {
        super("standardRules-hoare.key");
    }

    /**
     * returns all strategies supported by this profile
     */
    protected SetOfStrategyFactory getStrategyFactories() {
        return SetAsListOfStrategyFactory.EMPTY_SET.add(DEFAULT);
    }
    
    /**
     * returns the default strategy for this profile
     * @return the default strategy
     */
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }
    
    protected UpdateSimplificationRule getUpdateSimplificationRule() {
        return UpdateSimplificationRule.INSTANCE;
    }
    
    protected HoareLoopInvariantRule getInvariantRule() {
        return HoareLoopInvariantRule.INSTANCE;
    }
    
    protected ListOfBuiltInRule initBuiltInRules() {       
        
        // update simplifier
        ListOfBuiltInRule builtInRules = super.initBuiltInRules().
            prepend(getUpdateSimplificationRule());
  
        builtInRules = builtInRules.prepend(getInvariantRule());

        return builtInRules;
    }

    public String name() {       
        return "Hoare with Updates Profile";
    }

}
