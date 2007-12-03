package de.uka.ilkd.key.strategy;

import de.uka.ilkd.hoare.strategy.HoareLoopInvariantRuleFilter;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.ConditionalFeature;
import de.uka.ilkd.key.strategy.feature.Feature;

/** 
 * The HoareStrategy modifies and seals the JavaCardDLStrategy
 */
public class HoareStrategy extends JavaCardDLStrategy {

    public static final Name STRATEGY_NAME = new Name("HoareStrategy");
    
    public HoareStrategy(Proof p_proof, StrategyProperties strategyProperties) {
        super(p_proof, strategyProperties);     
        
        
    }
    
    /*protected Feature selectSimplifier(long cost) {
        return ConditionalFeature.createConditional(
                UpdateSimplificationRuleFilter.INSTANCE, inftyConst() );   
    }*/
    
    protected Feature[] getGlobalFSumComponents(Feature dispatcher, Proof p_proof) {
        final Feature[] components = super.getGlobalFSumComponents(dispatcher, p_proof);

        final Feature[] result = new Feature[components.length + 1];
        System.arraycopy(components, 0, result, 0, components.length);
        result[result.length - 1] = loopInvFeature(inftyConst());
      
        return result;        
    }
    
    
    private Feature loopInvFeature(Feature cost) {
        return ConditionalFeature.createConditional(
            HoareLoopInvariantRuleFilter.INSTANCE, cost );        
    }    
    
    public Name name() {
        return STRATEGY_NAME;        
    }
    
    
    public static class Factory extends StrategyFactory {
        public Factory () {
        }

        public Strategy create ( Proof p_proof, 
                StrategyProperties strategyProperties) { 
            
            StrategyProperties sp = new StrategyProperties();
            
            sp.put(StrategyProperties.SPLITTING_OPTIONS_KEY, 
                    StrategyProperties.SPLITTING_DELAYED);
            sp.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
            sp.put(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE);
            sp.put(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_NONE);

            boolean highPriority = false;
            
            try {
                highPriority = 
                    System.getenv("TEACHER_MODE") != null;
            } catch (Throwable t) {
                
            }
                       
            for (int i = 0; i < StrategyProperties.USER_TACLETS_NUM;i++) {
                sp.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(i), 
                        highPriority ? StrategyProperties.USER_TACLETS_HIGH :
                            StrategyProperties.USER_TACLETS_OFF);
            }
            
            sp.put(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
            sp.put(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);                       
            
            return new HoareStrategy ( p_proof, sp );
        }
        
        public Name name () {
            return STRATEGY_NAME;
        }
    }

}
