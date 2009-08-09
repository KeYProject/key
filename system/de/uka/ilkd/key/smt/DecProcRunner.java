// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;


import java.awt.event.ActionEvent;
import java.util.Timer;
import java.util.TimerTask;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.*;


/**
 * Runs the currently active decision procedure on 
 * each open goal of a given proof.
 */
public class DecProcRunner extends SwingWorker {

    private final IMain main;
    
    private final Proof proof;
    private int totalGoals = 0;
    private final KeYExceptionHandler exceptionHandler;
    
    private final Constraint userConstraint;
    private final BuiltInRule simpRule;

    public DecProcRunner(IMain main, Proof proof, Constraint userConstraint) {
	//instantiate this DecProcRunner with the currently selected standard SMT solver
        this(main, proof, userConstraint, null);
    }

    public DecProcRunner(IMain main, Proof proof, Constraint userConstraint, BuiltInRule r) {
        this.main = main;
        this.proof = proof;
        this.userConstraint = userConstraint;
        
        if (r == null) {
            this.simpRule = r;
        } else {
            this.simpRule = getIntegerDecisionProcedure();
        }
        exceptionHandler = main.mediator().getExceptionHandler();
    }
    
    public void run() {
        /* Invoking start() on the SwingWorker causes a new Thread
         * to be created that will call construct(), and then
         * finished().  Note that finished() is called even if
         * the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        //main.mediator().stopInterface(true);
        Object res = construct();
        finished(res);
    }

    public void finished(Object res) {
        final KeYMediator mediator = main.mediator();
        mediator.startInterface(true);		
        String msg = (String) res;
        if(!"".equals(msg)) {
            if(Main.batchMode){
                System.exit(-1);
            } else {
                new ExceptionDialog(Main.hasInstance() ? Main.getInstance() :
                    null, exceptionHandler.getExceptions());
                exceptionHandler.clear();
            }
        } else {
            int nrGoalsClosed = mediator.getNrGoalsClosedByAutoMode();
            main.setStatusLine( simpRule.displayName() + ": " + totalGoals + 
                    (totalGoals != 1 ? " goals" : " goal" ) + " processed, " + nrGoalsClosed + 
                    (nrGoalsClosed != 1 ? " goals" : " goal" )+ " could be closed!");
            if (nrGoalsClosed > 0 && !proof.closed()) {
                final String informationMsg =
                    nrGoalsClosed + ((nrGoalsClosed > 1) ? 
                            " goals have been closed": 
                    " goal has been closed");
                mediator.notify(
                        new GeneralInformationEvent(informationMsg));			   
            }

        }
    }
    
    public Object construct() {
        Object res = doWork();
        return res;
    }
    
    private Object doWork() {
        String status = "";
        main.mediator().stopInterface(true);
        final KeYMediator mediator = main.mediator();        
        mediator.resetNrGoalsClosedByHeuristics();
        InterruptListener il = null;
        	try {
                    try {
                        totalGoals = proof.openGoals().size();
                        int cnt = 0;
                        
                        proof.env().registerRule(simpRule,
                                de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);

                        main.setStatusLine("Running external decision procedure: " +
                                simpRule.displayName(), 99*totalGoals); 
                        
                        final IteratorOfGoal goals = proof.openGoals().iterator();

                        while (goals.hasNext()) {    
                            BuiltInRuleApp birApp = new BuiltInRuleApp(simpRule, null, 
                                    userConstraint);                    						
                            
                            Goal g = goals.next();
                            
                            cnt++;
                            final int temp = cnt;

                            //start a task to update the progressbar according to the timeprogress.
                            BaseProgressMonitor pm = null;
                            
                            //add a progress monitor to disply up to date progress.
                            if (simpRule instanceof SMTRule) {
                        	final SMTRule rule = (SMTRule) simpRule;
                        	il = new InterruptListener() {
                                    public void interruptionPerformed(ActionEvent e) {
                                        rule.interrupt();
                                        main.setStatusLine("External decision procedure interrupted by user");
                                    }
                                 };
                                main.mediator().addinterruptListener(il);
                        	int step = 99;
                		int base = (cnt-1) * step;
                		pm = new BaseProgressMonitor(base, main.getProgressMonitor());
                        	rule.addProgressMonitor(pm);
                            }
                            ProofTreeListener ptl = new ProofTreeListener() {
                        	
                        	public void proofGoalRemoved(ProofTreeEvent e) {
                        	    int step = 99;
                        	    main.getProgressMonitor().setProgress(step*temp);
                        	}
                        	
                        	public void proofIsBeingPruned(ProofTreeEvent e) {}
                        	public void proofPruned(ProofTreeEvent e) {}
                        	public void proofClosed(ProofTreeEvent e) {}
                        	public void proofStructureChanged(ProofTreeEvent e) {}
                        	public void proofGoalsAdded(ProofTreeEvent e) {}
                        	public void proofGoalsChanged(ProofTreeEvent e) {}
                        	public void proofExpanded(ProofTreeEvent e) {}
                            };
                            proof.addProofTreeListener(ptl);
                            g.apply(birApp);
                            if (il != null) {
                        	mediator.removeInterruptListener(il);
                        	il = null;
                            }
                            //remove the progress monitor again
                            if (pm != null) {
                        	((SMTRule)simpRule).removeProgressMonitor(pm);
                            }

                            proof.removeProofTreeListener(ptl);
                            
                        }
                    } catch (ExceptionHandlerException e) {
                        throw e;
                    } catch (Throwable thr) {
                        exceptionHandler.reportException(thr);
                    }
                } catch (ExceptionHandlerException ex){
                    main.setStatusLine("Running external decision procedure failed");
                    //status =  ex.toString();
                } finally {
                    if (il != null) {
                	mediator.removeInterruptListener(il);
                	il = null;
                    }
                    mediator.startInterface(true);
                }
        
        return status;
    }

    
    private BuiltInRule getIntegerDecisionProcedure() {
	final Name simpRuleName = proof.getSettings().getDecisionProcedureSettings().getActiveRule().getRuleName();
	final ListOfBuiltInRule rules = proof.getSettings().getProfile().getStandardRules().getStandardBuiltInRules();
        for (BuiltInRule r : rules) {
            if (r.name().equals(simpRuleName)) {
        	return r;
            }
        }	
        return null;
    }	

    /**
     * this ProgressMonitor adds the progress it gets to basevalue and passes it on to 
     * a registered progress monitor.
     * @author Simon Greiner
     *
     */
    private static class BaseProgressMonitor implements ProgressMonitor {
	
	private int baseval;
	private ProgressMonitor delegate;
	
	public BaseProgressMonitor(int baseval, ProgressMonitor delegate) {
	    this.baseval = baseval;
	    this.delegate = delegate;
	}
	
	public void setProgress(int val) {
	    delegate.setProgress(val+baseval);
	}
	    
	public void setMaximum(int val) {
	    //do nothing.
	}
	
    }
}
