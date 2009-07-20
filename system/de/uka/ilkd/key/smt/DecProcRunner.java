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

import java.util.Date;
import java.util.Timer;
import java.util.TimerTask;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;


/**
 * Runs the currently active decision procedure on 
 * each open goal of a given proof.
 */
public class DecProcRunner implements Runnable {

    private final IMain main;
    
    private final Proof proof;
    private int totalGoals = 0;
    private final KeYExceptionHandler exceptionHandler;
    
    private final Constraint userConstraint;
    private final BuiltInRule simpRule;

    public DecProcRunner(IMain main, Proof proof, Constraint userConstraint) {
        this.main = main;
        this.proof = proof;
        this.userConstraint = userConstraint;
        
        this.simpRule = getIntegerDecisionProcedure();
        exceptionHandler = main.mediator().getExceptionHandler();
    }

    public void run() {
        /* Invoking start() on the SwingWorker causes a new Thread
         * to be created that will call construct(), and then
         * finished().  Note that finished() is called even if
         * the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        main.mediator().stopInterface(true);
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
        
        final KeYMediator mediator = main.mediator();        
        mediator.resetNrGoalsClosedByHeuristics();
        try {
            try {
                totalGoals = proof.openGoals().size();
                int cnt = 0;
                
                proof.env().registerRule(simpRule,
                        de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);

                main.setStatusLine("Running external decision procedure: " +
                        simpRule.displayName(), 99); 
                
                final IteratorOfGoal goals = proof.openGoals().iterator();

                while (goals.hasNext()) {      
                    BuiltInRuleApp birApp = new BuiltInRuleApp(simpRule, null, 
                            userConstraint);                    						
                    
                    Goal g = goals.next();
                    
                    cnt++;
                    final int temp = cnt;
                    TimerTask tt = null;
                    Timer t = null;
                    //start a task to update the progressbar according to the timeprogress.
                    if (simpRule instanceof SMTRule) {
                	final SMTRule rule = (SMTRule) simpRule;
                	tt = new TimerTask() {
                	    public void run() {
                		int step = 99/totalGoals;
                		int base = (temp-1) * step;
                		int prog = base + (step*rule.getProgress())/99;
                		main.getProgressMonitor().setProgressImmediatly(prog);
                	    }
                	};
                	t = new Timer();
                	t.schedule(tt, 0, 300);
                    }
                    ProofTreeListener ptl = new ProofTreeListener() {
                	
                	public void proofGoalRemoved(ProofTreeEvent e) {
                	    int step = 100/totalGoals;
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
                    if (tt != null) {
                	tt.cancel();
                	t.cancel();
                	t = null;
                	tt = null;
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
            status =  ex.toString();
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






}
