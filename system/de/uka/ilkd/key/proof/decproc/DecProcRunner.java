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


import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;



public class DecProcRunner implements Runnable {

    Main main;
    KeYMediator mediator;
    String currentDecProc;
        
    Proof proof = null;
    int totalGoals = 0;
    KeYExceptionHandler exceptionHandler = null;
    
    private SwingWorker worker;

    public DecProcRunner(Main main) {
        this.main = main;
        mediator = main.mediator();
        currentDecProc = mediator.getProof().getSettings().getDecisionProcedureSettings()
                         .getDecisionProcedure();
        exceptionHandler = mediator.getExceptionHandler();
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
		mediator.startInterface(true);
		Main main = Main.getInstance();
		String msg = (String) get();
		if(!"".equals(msg)) {
		    if(Main.batchMode){
			System.exit(-1);
		    } else {
//                    mediator.notify(new GeneralFailureEvent(re.getMessage()));
			new ExceptionDialog(main, 
                                exceptionHandler.getExceptions());
			exceptionHandler.clear();
		    }
		} else {
		    int nrGoalsClosed = mediator.getNrGoalsClosedByAutoMode();
		    main.setStatusLine( currentDecProc + ": " + totalGoals + 
                (totalGoals != 1 ? " goals" : " goal" ) + " processed, " + nrGoalsClosed + 
                (nrGoalsClosed != 1 ? " goals" : " goal" )+ " could be closed!" );
		    if (nrGoalsClosed > 0 && !mediator.getProof().closed()) {
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
        mediator.stopInterface(true);
        worker.start();
    }



    private Object doWork() {
        String status = "";
        mediator.resetNrGoalsClosedByHeuristics();
        try {
            try {
                totalGoals = mediator.getProof().openGoals().size();
                int cnt = 0;
                IteratorOfGoal i = mediator.getProof().openGoals().iterator();
                BuiltInRule simpRule = null;
                mediator.stopInterface(true);
                mediator.setInteractive(false);
                main.setStatusLine("Running external decision procedure: " +
                        currentDecProc, totalGoals);
                while (i.hasNext()) {      
                    //AR: %% GUI-Rule separation, many rule instances:
                    if (mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useSimplify())
                        simpRule = new SimplifyIntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());
                    else if (mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useICS())
                        simpRule = new ICSIntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());
                    else if (mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useCVCLite())
                        simpRule = new CVCLiteIntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());
                    else if (mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useCVC3())
                        simpRule = new CVC3IntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());
                    else if (mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useSVC())
                        simpRule = new SVCIntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());
                    else if ( mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useYices())
                        simpRule = new YicesIntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());
                    else if (mediator.getProof().getSettings().getDecisionProcedureSettings()
                            .useSMT_Translation())
                        simpRule = new SmtTranslationIntegerRule(false,
                                new JavaDecisionProcedureTranslationFactory());

                    BuiltInRuleApp birApp = new BuiltInRuleApp(simpRule, null, mediator
                            .getUserConstraint().getConstraint());
                    mediator.getProof().env().registerRule(simpRule,
                            de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);						
                    i.next().apply(birApp);
                    cnt++;
                    main.getProgressMonitor().setProgress(cnt);
                }
//              main.setStandardStatusLine();
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






}
