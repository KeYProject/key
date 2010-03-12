// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.smt;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.nodeviews.BuiltInRuleMenuItem;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTRuleNew;


public class RuleLauncher {
    
    	    public static final RuleLauncher INSTANCE = new RuleLauncher();
    	    
    	    private RuleLauncher(){
    		
    	    }
    	    
    	    
    	    public void start(SMTRuleNew rule, Goal goal, Constraint constraint){
    		LinkedList<Goal> goals = new LinkedList<Goal>();
    		goals.add(goal);
    		rule.start(goal,constraint);
    		startProgressDialog(rule,goals);
    	    }
    	    
    	    public void start(SMTRuleNew rule, Proof proof, Constraint constraint){
    		LinkedList<Goal> goals = new LinkedList<Goal>();
    		
    		for (Goal goal : proof.openGoals()) {
    		     goals.add(goal);
    		}
    		
    		rule.start(goals,proof,constraint);
    		startProgressDialog(rule,goals);
    		
    	    }
    	    
    	    private void startProgressDialog(SMTRuleNew rule, Collection<Goal> goals){
    		ProgressDialog.INSTANCE.prepare(rule.getInstalledSolvers(),goals,rule);
    		ProgressDialog.INSTANCE.showDialog();
    	    }
    
    
	

}
