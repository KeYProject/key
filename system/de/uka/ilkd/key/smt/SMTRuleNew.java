// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.smt.launcher.Process;
import de.uka.ilkd.key.smt.launcher.ProcessLauncher;

class BuiltInRuleAppSMT extends BuiltInRuleApp{
    final SMTSolverResult result;
    public BuiltInRuleAppSMT(BuiltInRule builtInRule, PosInOccurrence pio,
            Constraint userConstraint, SMTSolverResult result) {
	super(builtInRule, pio, userConstraint);
	this.result = result;
    }
    public SMTSolverResult getResult(){return result;}
    
}


public class SMTRuleNew  extends ProcessLauncher implements BuiltInRule{

    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
    private Constraint 	           userConstraint = null;
    private Proof		   proof;
    
    
    
    public SMTRuleNew(SMTSolver ... list){
	for(SMTSolver solver : list){
	   solvers.add(solver);   
	}
    }
    

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
            Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }


    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {
	
	assert ruleApp instanceof BuiltInRuleAppSMT;
	
	SMTSolverResult result = ((BuiltInRuleAppSMT)ruleApp).getResult();
	
	if (result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) {
	    return ImmutableSLList.<Goal>nil();
	} else {
	    return null;
	}
    }

    private void addSolver(SMTSolver solver, Collection<Goal> goals, Services services){
	solver.prepareSolver(goals, services);
	addProcess(solver);	
    }
    
    private void prepareSolvers(Collection<Goal> goals, Services services){
	for(SMTSolver solver : solvers){
	    addSolver(solver,goals,services);
	}
    }
    
    public void start(Goal goal, Constraint constraint){
	LinkedList<Goal> goals = new LinkedList<Goal>();
	goals.add(goal);
	proof = goal.proof();
	startThread(goals,constraint);
    }
    
    public void start(Proof proof, Constraint constraint){
	LinkedList<Goal> goals = new LinkedList<Goal>();
	this.proof = proof;
	for (Goal goal : proof.openGoals()) {
	     goals.add(goal);
	}
	
	
	startThread(goals,constraint);
    }
    
    private void startThread(Collection<Goal> goals,Constraint constraint){
	userConstraint = constraint;
        proof.env().registerRule(this,
                de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);
	prepareSolvers(goals,proof.getServices());	
	Thread thread = new Thread(this,displayName());
	thread.start();
    }
    
    

    public String displayName() {
	String s = "NEW: ";
	for(SMTSolver solver : solvers){
	    s += solver.name()+" ";
	}
	return s;
    }

    
    public Name name() {
	
	return new Name(displayName());
    }
    
    public String getTitle(){
	return  displayName();
    }
    

    @Override
    public void eventCycleFinished(Process p) {
        AbstractSMTSolver solver = (AbstractSMTSolver)p;
        SMTSolverResult result = solver.getSession().getResults().getLast();
        BuiltInRuleApp birApp = new BuiltInRuleAppSMT(this, null, 
                userConstraint,result); 
        solver.getSession().currentGoal().apply(birApp);
        super.eventCycleFinished(p);
    }
    
    
 
    
    

 
    

}
