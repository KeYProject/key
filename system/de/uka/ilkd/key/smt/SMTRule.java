//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.ProgressMonitor;

public class SMTRule implements BuiltInRule, MakesProgress {

    private final SMTSolver solver;


    
    public SMTRule(SMTSolver arg1) {
	this.solver = arg1;
    }
    
    /** 
     * @return solver associated with the instance.
     */
    public SMTSolver getSolver(){
	return solver;
    }

    /**
     * This rule's name.
     */
    public String displayName() {
	return solver.name();
    }

    /**
     * This rule's name as Name object.
     */
    public Name name() {
	return new Name(displayName());
    }

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
	    Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }

    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
	int timeout = ProofSettings.DEFAULT_SETTINGS
	                           .getDecisionProcedureSettings()
	                           .getTimeout()*100;
	TacletSetTranslation tacletSetTranslation = new DefaultTacletSetTranslation();
	tacletSetTranslation.setTacletSet(goal.proof().env().getInitConfig().getTaclets());
	
	tacletSetTranslation.addHeuristic("smt_axiom_not_verified");
	this.solver.setTacletSetTranslation(tacletSetTranslation);
		
	SMTSolverResult result = SMTSolverResult.NO_IDEA;	
	try {
	    result = this.solver.run(goal, timeout, services);
	} catch (IOException ioe) {	    	    
	    if (services.getExceptionHandler() != null) {
		services.getExceptionHandler().reportException(ioe);
	    } else {
		RuntimeException re = new RuntimeException(ioe.getMessage());
		re.initCause(ioe);
		throw re;
	    }	    
	}
	if (result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) {
	    return ImmutableSLList.<Goal>nil();
	} else {
	    return null;
	}
    }
    
    /**
     * add a monitor to watch the Progress in the execution.
     * During execution, all registered monitors are set to values between 0 and 99.
     * @param p
     */
    public void addProgressMonitor(ProgressMonitor p) {
	this.solver.addProgressMonitor(p);
    }
    
    /**
     * remove a registered progress monitor.
     * @param p
     * @return true, if remove was successful.
     */
    public boolean removeProgressMonitor(ProgressMonitor p) {
	return this.solver.removeProgressMonitor(p);
    }
    
    /**
     * remove all registered progress monitors.
     *
     */
    public void removeAllProgressMonitors() {
	this.solver.removeAllProgressMonitors();
    }
    
    public String toString() {
	return name().toString();
    }
    
    /**
     * check, if this solver is installed and can be used.
     * @param recheck if false, the solver is not checked again, if a cached value for this exists.
     * @return true, if it is installed.
     */
    public boolean isInstalled(boolean recheck) {
	return this.solver.isInstalled(recheck);
    }
    
    /**
     * returns the hard coded execution format.
     * @return the hard coded execution command.
     */
    public String defaultExecutionCommand() {
	return this.solver.getDefaultExecutionCommand();
    }
    
    /**
     * 
     * @return the progress made on the current task. Value 0..99
     */
    public int getProgress() {
	if (this.solver != null) {
	    return this.solver.getProgress();
	} else {
	    return 0;
	}
    }
    
    /**
     * Interrupt the running rule.
     *
     */
    public void interrupt() {
	this.solver.interrupt();
    }
}
