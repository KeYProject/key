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

package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.DefaultGoalChooserBuilder;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppModPositionFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;

// TODO: Discuss settings and improve the code layout.
/**
 * Strategy tailored to VBT aimed symbolic execution.
 */
public class VBTStrategy extends JavaCardDLStrategy {

    /** This is the default value when changing back from a different Strategy back to VBTStrategy.
     * The value can be changed via the command option "loop". It is set in JavaTestGenerationProfile.
     * @see de.uka.ilkd.key.proof.init.JavaTestGenerationProfile */
    public static String preferedGoalChooser=DefaultGoalChooserBuilder.NAME;//Maybe set to BalancedGoalChooser. But on the other hand this can be set via the option "loop".
   
    /** if false then the normal loop unwinding rule is used. Otherwise bounded loop unwinding is activated. This
     * flag activates the respective rule in testGenOpt.key when calling the method setupStrategyProperties(); 
     * @see de.uka.ilkd.key.rule.metaconstruct.WhileLoopTransformation2
     * @see de.uka.ilkd.key.proof.init.JavaTestGenerationProfile */
    public static boolean loopUnwindBounded=false;

    /**mode 0 is the more or less original version by engel, mode 1 is closer to the JavaCardDLStrategy and rule set.*/
    private int vbtMode=0;
    
    /**Warning. The name VBTStrategy is used only if {@code vbtMode==0} */
    public static String VBTStrategy="VBTStrategy";
    
    protected static StrategyProperties setupStrategyProperties() {
        final StrategyProperties res = new StrategyProperties ();
        res.setProperty( StrategyProperties.SPLITTING_OPTIONS_KEY,
                StrategyProperties.SPLITTING_NORMAL);
        if(loopUnwindBounded){
            res.setProperty ( StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_EXPAND_BOUNDED );
        }else{
            res.setProperty ( StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_EXPAND);
        }
        res.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_EXPAND);
        res.setProperty ( StrategyProperties.METHOD_OPTIONS_KEY,
                          StrategyProperties.METHOD_EXPAND );
        res.setProperty ( StrategyProperties.QUERY_OPTIONS_KEY,
                          StrategyProperties.QUERY_OFF );
        res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, 
                        StrategyProperties.QUANTIFIERS_INSTANTIATE);
        return res;
    }
    
    protected VBTStrategy(Proof p_proof, StrategyProperties strategyProperties, final int mode) {
        super(p_proof, strategyProperties);
        vbtMode = mode;
        final RuleSetDispatchFeature rsd = getCostComputationDispatcher();
        if(mode==0){
            clearRuleSetBindings (rsd, "test_gen" );
            bindRuleSet (rsd, "test_gen",
                          add ( longConst ( -1000 ),
                                NonDuplicateAppModPositionFeature.INSTANCE));

            clearRuleSetBindings (rsd, "test_gen_empty_modality_hide" );
            bindRuleSet (rsd, "test_gen_empty_modality_hide",
                          add ( longConst ( -1000 ),
                                NonDuplicateAppModPositionFeature.INSTANCE));
            
            clearRuleSetBindings (rsd, "test_gen_quan" );
            bindRuleSet (rsd, "test_gen_quan",
                          add ( longConst ( -1000 ),
                                NonDuplicateAppModPositionFeature.INSTANCE));

            
            clearRuleSetBindings (rsd, "test_gen_quan_num" );
            bindRuleSet (rsd, "test_gen_quan_num",
                          add ( longConst ( 30000 ),
                                NonDuplicateAppModPositionFeature.INSTANCE));
            
            clearRuleSetBindings (rsd, "split_cond" );
            bindRuleSet (rsd, "split_cond", -1000);
            
            clearRuleSetBindings (rsd, "split" );
            bindRuleSet (rsd, "split", -1000);
    
            clearRuleSetBindings (rsd, "beta" );
            bindRuleSet (rsd, "beta", -1000);
        
//            clearRuleSetBindings (rsd, "inReachableStateImplication" ); // Do not change this rule behavior because if it is enabled branches with negative array length are not closed.
//            bindRuleSet (rsd, "inReachableStateImplication", inftyConst());
            clearRuleSetBindings (rsd, "cut_direct" );
            bindRuleSet (rsd, "cut_direct",inftyConst());
    
            clearRuleSetBindings (rsd, "simplify_prog" );
            bindRuleSet (rsd, "simplify_prog",10000);
            
            clearRuleSetBindings (rsd, "simplify_prog_subset" );
            bindRuleSet (rsd, "simplify_prog_subset",10000);
        }else if(mode==1){
//            boolean vbt_sym_ex = strategyProperties.getProperty(
//                    			StrategyProperties.VBT_PHASE).
//                    		equals(StrategyProperties.VBT_SYM_EX);
            boolean vbt_quan_inst = strategyProperties.getProperty(
					StrategyProperties.VBT_PHASE).
					equals(StrategyProperties.VBT_QUAN_INST);
            boolean vbt_model_gen = strategyProperties.getProperty(
					StrategyProperties.VBT_PHASE).
					equals(StrategyProperties.VBT_MODEL_GEN);

            //System.out.println("VBTStrategy(1) sym_ex:"+vbt_sym_ex+" quan_inst:"+vbt_quan_inst+" model_gen:"+vbt_model_gen);

            clearRuleSetBindings (rsd, "test_gen_empty_modality_hide" );
            bindRuleSet (rsd, "test_gen_empty_modality_hide", inftyConst());
            
            clearRuleSetBindings (rsd, "test_gen" );
            bindRuleSet (rsd, "test_gen",
                          add ( longConst (-100 ),
                                NonDuplicateAppModPositionFeature.INSTANCE));

            clearRuleSetBindings (rsd, "test_gen_quan" );
            bindRuleSet (rsd, "test_gen_quan",
        	    		vbt_quan_inst?
        	    			add( longConst ( -1000 ),NonDuplicateAppModPositionFeature.INSTANCE)
            				:inftyConst());
            
            clearRuleSetBindings (rsd, "test_gen_quan_num" );
            bindRuleSet (rsd, "test_gen_quan_num",
                          	vbt_quan_inst?
                          		add ( longConst ( -100 ),NonDuplicateAppModPositionFeature.INSTANCE)
                          		:inftyConst());
            
            if(vbt_quan_inst || vbt_model_gen){
                clearRuleSetBindings (rsd, "simplify_expression" );
                bindRuleSet (rsd, "simplify_expression", inftyConst());        	

                clearRuleSetBindings (rsd, "simplify_prog" );
                bindRuleSet (rsd, "simplify_prog", inftyConst());        	

                clearRuleSetBindings (rsd, "simplify_prog_subset" );
                bindRuleSet (rsd, "simplify_prog_subset", inftyConst());
                
                clearRuleSetBindings (rsd, "simplify_autoname" );
                bindRuleSet (rsd, "simplify_autoname", inftyConst());

                clearRuleSetBindings (rsd, "loop_expand" );
                bindRuleSet (rsd, "loop_expand", inftyConst());
                
                /*clearRuleSetBindings (rsd, "block_expand" );
                bindRuleSet (rsd, "block_expand", inftyConst());*/

                clearRuleSetBindings (rsd, "loop_expand_bounded" );
                bindRuleSet (rsd, "loop_expand_bounded", inftyConst());

                clearRuleSetBindings (rsd, "method_expand" );
                bindRuleSet (rsd, "method_expand", inftyConst());
            }

//            if(vbt_model_gen){
//                clearRuleSetBindings (rsd, "split_cond" );
//                bindRuleSet (rsd, "split_cond", -1000);
//                
//                clearRuleSetBindings (rsd, "split" );
//                bindRuleSet (rsd, "split", -1000);
//        
//                clearRuleSetBindings (rsd, "beta" );
//                bindRuleSet (rsd, "beta", -1000);
//            }
        }
    }
    

    protected boolean arithDefOps() {
	return true;
    }   
    
    public Name name () {
        switch(vbtMode){
        case 0: return new Name(VBTStrategy); 
        case 1: return new Name(JavaCardDLStrategy); 
        default: throw new RuntimeException("Unknwon VBT mode:"+vbtMode);
        }
    }

    public static class Factory extends StrategyFactory {

	/**mode 0 is the more or less original version by engel, mode 1 is closer to the JavaCardDLStrategy and rule set.*/
	private int vbtMode=0;
	/**Version 0 is for verification-based testing as it was originally implemented and it differs from the normal JavaCardDLStrategy 
	 * Version 1 is closer to the normal JavaCardDLStrategy*/
        public Factory (int version) {
            assert version==0||version==1;
            this.vbtMode = version;
	}

        public Strategy create ( Proof p_proof, 
                StrategyProperties strategyProperties ) {
            if(vbtMode==0)
        	return new VBTStrategy ( p_proof,setupStrategyProperties (), vbtMode);
            else if(vbtMode==1)
        	return new VBTStrategy ( p_proof, strategyProperties, vbtMode);
            else 
        	return null;
        }
        
        public Name name () {
            switch(vbtMode){
            case 0: return new Name(VBTStrategy); 
            case 1: return new Name(JavaCardDLStrategy); 
            default: throw new RuntimeException("Unknwon VBT mode:"+vbtMode);
            }
        }
    }
}