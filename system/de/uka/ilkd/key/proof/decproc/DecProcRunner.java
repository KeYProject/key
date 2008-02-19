// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;


import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;



public class DecProcRunner implements Runnable {

    private final IMain main;
    private final String currentDecProc;

    private final Proof proof;
    private int totalGoals = 0;
    private final KeYExceptionHandler exceptionHandler;

    private SwingWorker worker;
    
    private final Constraint userConstraint;
    private final BuiltInRule simpRule;

    public DecProcRunner(IMain main, Proof proof, 
            Constraint userConstraint, String decisionProcedure) {
        this.main = main;
        this.proof = proof;
        this.userConstraint = userConstraint;
        
        this.simpRule = getIntegerDecisionProcedure();
        
        currentDecProc = decisionProcedure;             
        exceptionHandler = main.mediator().getExceptionHandler();
    }

    public void run() {
        /* Invoking start() on the SwingWorker causes a new Thread
         * to be created that will call construct(), and then
         * finished().  Note that finished() is called even if
         * the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        worker = new SwingWorker() {
            public Object construct() {
                Object res = doWork();
                return res;
            }
            public void finished() {
                final KeYMediator mediator = main.mediator();
                mediator.startInterface(true);		
                String msg = (String) get();
                if(!"".equals(msg)) {
                    if(Main.batchMode){
                        System.exit(-1);
                    } else {
//                      mediator.notify(new GeneralFailureEvent(re.getMessage()));
                        new ExceptionDialog(Main.hasInstance() ? Main.getInstance() :
                            null, exceptionHandler.getExceptions());
                        exceptionHandler.clear();
                    }
                } else {
                    int nrGoalsClosed = mediator.getNrGoalsClosedByAutoMode();
                    main.setStatusLine( currentDecProc + ": " + totalGoals + 
                            (totalGoals != 1 ? " goals" : " goal" ) + " processed, " + nrGoalsClosed + 
                            (nrGoalsClosed != 1 ? " goals" : " goal" )+ " could be closed!" );
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
        };
        main.mediator().stopInterface(true);
        worker.start();
    }



    private Object doWork() {
        String status = "";
        
        final KeYMediator mediator = main.mediator();        
        mediator.resetNrGoalsClosedByHeuristics();
        try {
            try {
                totalGoals = proof.openGoals().size();
                int cnt = 0;
                mediator.stopInterface(true);
                mediator.setInteractive(false);
                main.setStatusLine("Running external decision procedure: " +
                        currentDecProc, totalGoals);
                
                // TODO: use always only one rule instance and register the rule at 
                // a central place 
                proof.env().registerRule(simpRule,
                        de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);
                
                final IteratorOfGoal goals = proof.openGoals().iterator();
                while (goals.hasNext()) {      
                    BuiltInRuleApp birApp = new BuiltInRuleApp(simpRule, null, 
                            userConstraint);                    						
                    goals.next().apply(birApp);
                    cnt++;
                    main.getProgressMonitor().setProgress(cnt);
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


    // TODO remove creation of new rules
    private BuiltInRule getIntegerDecisionProcedure() {
        BuiltInRule rule = null;
        final DecisionProcedureSettings decProcSettings = proof.getSettings()
                .getDecisionProcedureSettings();
        if (decProcSettings.useSimplify())
            rule = new SimplifyIntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        else if (decProcSettings.useICS())
            rule = new ICSIntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        else if (decProcSettings.useCVCLite())
            rule = new CVCLiteIntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        else if (decProcSettings.useCVC3())
            rule = new CVC3IntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        else if (decProcSettings.useSVC())
            rule = new SVCIntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        else if (decProcSettings.useYices())
            rule = new YicesIntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        else if (decProcSettings.useSMT_Translation())
            rule = new SmtTranslationIntegerRule(false,
                    new JavaDecisionProcedureTranslationFactory());
        return rule;
    }






}
