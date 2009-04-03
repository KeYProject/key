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


import java.util.Timer;
import java.util.TimerTask;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
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
                        simpRule.displayName(), totalGoals); 
                
                final IteratorOfGoal goals = proof.openGoals().iterator();
                while (goals.hasNext()) {      
                    BuiltInRuleApp birApp = new BuiltInRuleApp(simpRule, null, 
                            userConstraint);                       
                    goals.next().apply(birApp);
                    cnt++;
                   
                    main.setStatusLine("Running external decision procedure: " +
                            simpRule.displayName(), cnt); 
                    
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
        BuiltInRule rule = proof.getSettings().getDecisionProcedureSettings().getActiveRule();
        return rule;
    }






}
