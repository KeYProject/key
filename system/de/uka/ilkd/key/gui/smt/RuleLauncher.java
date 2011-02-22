//// This file is part of KeY - Integrated Deductive Software Design
//// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
////                         Universitaet Koblenz-Landau, Germany
////                         Chalmers University of Technology, Sweden
////
//// The KeY system is protected by the GNU General Public License. 
//// See LICENSE.TXT for details.
////
////
//package de.uka.ilkd.key.gui.smt;
//
//import java.util.Collection;
//import java.util.LinkedList;
//
//import de.uka.ilkd.key.logic.Constraint;
//import de.uka.ilkd.key.proof.Goal;
//import de.uka.ilkd.key.proof.Proof;
//import de.uka.ilkd.key.smt.SMTRule;
//import de.uka.ilkd.key.smt.SMTRule.WaitingPolicy;
//
///**
// * Use this class to start SMTRules, if you want to use SMTSolver in KeY
// * by user interaction.
// * It belongs to de.uka.ilkd.gui... because it contains the mechanism 
// * to start SMTRules in combination with <code>ProgressDialog</code>
// */
//public class RuleLauncher {
//    
//    	    public static final RuleLauncher INSTANCE = new RuleLauncher();
//    	    
//    	    private RuleLauncher(){
//    		
//    	    }
//    	    
//    	    public WaitingPolicy getApplyPolicy(){
//    
//    		if(SMTSettings.getInstance().getProgressDialogMode()
//    			== SMTSettings.PROGRESS_MODE_CLOSE_FIRST)
//    		return WaitingPolicy.STOP_FIRST;
//    		return WaitingPolicy.WAIT_FOR_ALL;
//    		
//    	    }
//    	    
//    	    /**
//    	     * Launches first the SMTRule and then the ProgressDialog is shown.
//    	     * @param rule the rule to be launched
//    	     * @param goal 
//    	     * @param constraint
//    	     */
//    	    public void start(SMTRule rule, Goal goal, Constraint constraint, boolean useOwnThread){
//    		if(!rule.isUsable()){
//    		    return;
//    		}
//    		LinkedList<Goal> goals = new LinkedList<Goal>();
//    		rule.setMaxTime(SMTSettings.getInstance().getTimeout()*100);
//    		goals.add(goal);
//       		rule.start(goal,constraint,useOwnThread,getApplyPolicy());
//    		if(useOwnThread){
//    		    startProgressDialog(rule,goals);    
//    		}
//    		
//    	    }
//    	    
//    	    public void start(SMTRule rule, Proof proof, Constraint constraint, boolean useOwnThread){
//    		if(!rule.isUsable()){
//    		    return;
//    		}
//    		LinkedList<Goal> goals = new LinkedList<Goal>();
//    		rule.setMaxTime(SMTSettings.getInstance().getTimeout()*100);
//    		for (Goal goal : proof.openGoals()) {
//    		     goals.add(goal);
//    		}
//  
//    		rule.start(goals,proof,constraint,useOwnThread,getApplyPolicy());
//    		if(useOwnThread){
//    		    startProgressDialog(rule,goals);
//    		}
//    		
//    		
//    	    }
//    	    
//    	    
//    	    
//    	    private void startProgressDialog(SMTRule rule, Collection<Goal> goals){
//    		//ProgressDialog.INSTANCE.prepare(rule.getInstalledSolvers(),goals,rule);
//    		ProgressDialog.INSTANCE.showDialog();
//    	    }
//    
//    
//	
//
//}
