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

package de.uka.ilkd.key.gui;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.AbstractUserInterface;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/**
 * This class is the starting point for the extraction of a unified
 * Userinterface for a GUI refactoring.
 *
 * It gathers all present interfaces and redirects action to the mainWindow.
 *
 * It is subject to change a lot at the moment.
 *
 * @author mattias ulbrich
 */

public class WindowUserInterface extends AbstractUserInterface {

	private MainWindow mainWindow;


    private LinkedList<InteractiveRuleApplicationCompletion> completions =
            new LinkedList<InteractiveRuleApplicationCompletion>();

	public WindowUserInterface(MainWindow mainWindow) {
		this.mainWindow = mainWindow;
	        completions.add(new FunctionalOperationContractCompletion());
		completions.add(new DependencyContractCompletion());
		completions.add(new LoopInvariantRuleCompletion());
		completions.add(new BlockContractCompletion(mainWindow));
	}

	public void loadProblem(File file, List<File> classPath,
	        File bootClassPath) {
		mainWindow.addRecentFile(file.getAbsolutePath());
		super.loadProblem(
		        file, classPath, bootClassPath, mainWindow.getMediator());
	}

	@Override
	public void loadProblem(File file) {
		loadProblem(file, null, null);
	}

	@Override
	public void progressStarted(Object sender) {
		mainWindow.getMediator().stopInterface(
		        true);
	}

	@Override
	public void progressStopped(Object sender) {
		mainWindow.getMediator().startInterface(
		        true);
	}

	@Override
	public void proofCreated(ProblemInitializer sender,
	        ProofAggregate proofAggregate) {
		mainWindow.addProblem(proofAggregate);
		mainWindow.setStandardStatusLine();
	}

	@Override
	public void reportException(Object sender, ProofOblInput input, Exception e) {
		reportStatus(
		        sender, input.name() + " failed");
	}

	@Override
	public void reportStatus(Object sender, String status, int progress) {
		mainWindow.setStatusLine(
		        status, progress);
	}

	@Override
	public void reportStatus(Object sender, String status) {
		mainWindow.setStatusLine(status);
	}

	@Override
	public void resetStatus(Object sender) {
		mainWindow.setStandardStatusLine();
	}

	@Override
	public void taskFinished(TaskFinishedInfo info) {
		if (info.getSource() instanceof ApplyStrategy) {
			resetStatus(this);
			ApplyStrategy.ApplyStrategyInfo result = (ApplyStrategyInfo) info
			        .getResult();

			Proof proof = info.getProof();
			if (!proof.closed()) {
				Goal g = result.nonCloseableGoal();
				if (g == null) {
					g = proof.openGoals().head();
				}
				mainWindow.getMediator().goalChosen(g);
				if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
					// iff Stop on non-closeable Goal is selected a little
					// popup is generated and proof is stopped
					AutoDismissDialog dialog = new AutoDismissDialog(
					        "Couldn't close Goal Nr. " + g.node().serialNr()
					                + " automatically");
					dialog.show();
				}
			}
			mainWindow.displayResults(info.toString());
		} else if (info.getSource() instanceof ProblemLoader) {
			if (info.getResult() != null) {
				final KeYExceptionHandler exceptionHandler = ((ProblemLoader) info
				        .getSource()).getExceptionHandler();
				ExceptionDialog.showDialog(
				        mainWindow, exceptionHandler.getExceptions());
				exceptionHandler.clear();
			} else {
				resetStatus(this);
				KeYMediator mediator = mainWindow.getMediator();
				mediator.getNotationInfo().refresh(
				        mediator.getServices());
			}
		} else {
			resetStatus(this);
			if (!info.toString().isEmpty()) {
				mainWindow.displayResults(info.toString());
			}
		}
	}

	protected boolean inStopAtFirstUncloseableGoalMode(Proof proof) {
		return proof.getSettings().getStrategySettings()
		        .getActiveStrategyProperties().getProperty(
		                StrategyProperties.STOPMODE_OPTIONS_KEY).equals(
		                StrategyProperties.STOPMODE_NONCLOSE);
	}

	@Override
	public void taskProgress(int position) {
		mainWindow.getStatusLine().setProgress(
		        position);

	}

	@Override
	public void taskStarted(String message, int size) {
		mainWindow.setStatusLine(
		        message, size);
	}

	@Override
	public void setMaximum(int maximum) {
		mainWindow.getStatusLine().setProgressBarMaximum(
		        maximum);
	}

	@Override
	public void setProgress(int progress) {
		mainWindow.getStatusLine().setProgress(
		        progress);
	}

	@Override
	public void notifyAutoModeBeingStarted() {
		mainWindow.setCursor(new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR));
	}

	@Override
	public void notifyAutomodeStopped() {
		mainWindow
		        .setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
	}

	@Override
	public void notify(NotificationEvent event) {
		mainWindow.notify(event);
	}

	@Override
	public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models,
	        Goal goal) {
		new TacletMatchCompletionDialog(mainWindow, models, goal,
		        mainWindow.getMediator());
	}

	@Override
	public boolean confirmTaskRemoval(String string) {
		int answer = JOptionPane.showConfirmDialog(
		        MainWindow.getInstance(), string, "Abandon Proof",
		        JOptionPane.YES_NO_OPTION);
		return answer == JOptionPane.YES_OPTION;
	}

	@Override
	public void openExamples() {
		mainWindow.openExamples();
	}

	@Override
	public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
	    if (mainWindow.getMediator().autoMode()) {
	        return super.completeBuiltInRuleApp(app, goal, forced);
	    }

	    IBuiltInRuleApp result = app;
	    for (InteractiveRuleApplicationCompletion compl : completions ) {
	        if (compl.canComplete(app)) {
	            result = compl.complete(app, goal, forced);
	            break;
	        }
	    }
	    return (result != null && result.complete()) ? result : null;
	}

	@Override
	public ProblemInitializer createProblemInitializer(Profile profile) {
	    ProblemInitializer pi = new ProblemInitializer(this,
	            new Services(profile, mainWindow.getMediator().getExceptionHandler()),
	            true,
	            this);
	    return pi;
	}

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
      return mainWindow.getMediator();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DefaultProblemLoader load(Profile profile, File file, List<File> classPath, File bootClassPath) throws ProblemLoaderException {
      if (file != null) {
         mainWindow.getRecentFiles().addRecentFile(file.getAbsolutePath());
      }
      return super.load(profile, file, classPath, bootClassPath);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAutoModeSupported(Proof proof) {
      return mainWindow.getProofList().containsProof(proof);
   }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeProof(Proof proof) {
        if (!proof.isDisposed()) {
           // The following was copied from AbandonTaskAction when I redirected
           // the abandon method there to this method.
           // The code seems to do more than the original code of this method...
           final TaskTreeNode rootTask = proof.getBasicTask().getRootTask();
           mainWindow.getProofList().removeTask(rootTask);
           final Proof[] rootTaskProofs = rootTask.allProofs();
           for (Proof p : rootTaskProofs) {
               //In a previous revision the following statement was performed only
               //on one proof object, namely on: mediator.getProof()
               p.dispose();
           }
           proof.dispose();
           mainWindow.getProofView().removeProofs(rootTaskProofs);

           // The original code of this method. Neccessary?
           mainWindow.getProofList().removeProof(proof);

           // Run the garbage collector.
           Runtime r = Runtime.getRuntime();
           r.gc();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isRegisterProofs() {
       return true;
    }
}
