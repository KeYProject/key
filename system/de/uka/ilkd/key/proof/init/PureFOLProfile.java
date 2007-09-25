package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.strategy.FOLStrategy;
import de.uka.ilkd.key.strategy.SetOfStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;

public class PureFOLProfile extends AbstractProfile {
   
    private final static StrategyFactory DEFAULT = new FOLStrategy.Factory();
    
    public PureFOLProfile() {
        super("standardRules-FOL.key");       
    }

    public String name() {
        return "Pure FOL Profile";
    }

    protected SetOfStrategyFactory getStrategyFactories() {  
        return super.getStrategyFactories().
            add(DEFAULT);
    }  
       
    public StrategyFactory getDefaultStrategyFactory() {        
        return DEFAULT;
    }
}
