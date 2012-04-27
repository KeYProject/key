package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.IOException;
import java.util.List;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
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

	public WindowUserInterface(MainWindow mainWindow) {
		this.mainWindow = mainWindow;
	}

	public void loadProblem(File file, List<File> classPath,
	        File bootClassPath) {
		mainWindow.addRecentFile(file.getAbsolutePath());
		super.loadProblem(
		        file, classPath, bootClassPath, mainWindow.getMediator());
	}

	@Override
	public void loadProblem(File file) {
		loadProblem(
		        file, null, null, mainWindow.getMediator());
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
				mainWindow.getMediator().goalChosen(
				        g);
				if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
					// iff Stop on non-closeable Goal is selected a little
					// popup is generated and proof is stopped
					AutoDismissDialog dialog = new AutoDismissDialog(
					        "Couldn't close Goal Nr. " + g.node().serialNr()
					                + " automatically");
					dialog.show();
				}
			}
			mainWindow.displayResults(
			        info.getTime(), info.getAppliedRules(),
			        info.getClosedGoals(), info.getProof().openGoals().size());
		} else if (info.getSource() instanceof ProblemLoader) {
			if (!"".equals(info.getResult())) {
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
			if (info.toString() != "") {
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

	private static PosInOccurrence letUserChooseStep(
	        List<PosInOccurrence> steps, Services services) {
		// prepare array of possible base heaps
		final TermStringWrapper[] heaps = new TermStringWrapper[steps.size()];
		int i = 0;
		final LogicPrinter lp = new LogicPrinter(null, new NotationInfo(),
		        services);
		lp.setLineWidth(120);
		for (PosInOccurrence step : steps) {
			final Term heap = step.subTerm().sub(0);
			lp.reset();
			try {
				lp.printTerm(heap);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
			String prettyprint = lp.toString();
			prettyprint = "<html><tt>" + LogicPrinter.escapeHTML(
			        prettyprint, true) + "</tt></html>";
			heaps[i++] = new TermStringWrapper(heap, prettyprint);
		}

		// open dialog
		final TermStringWrapper heapWrapper = (TermStringWrapper) JOptionPane
		        .showInputDialog(
		                MainWindow.getInstance(), "Please select a base heap:",
		                "Instantiation", JOptionPane.QUESTION_MESSAGE, null,
		                heaps, heaps.length > 0 ? heaps[0] : null);
		
		if (heapWrapper == null) {
			return null;
		}
		final Term heap = heapWrapper.term;

		// find corresponding step
		for (PosInOccurrence step : steps) {
			if (step.subTerm().sub(0).equals(heap)) {
				return step;
			}
		}
		assert false;
		return null;
	}

	@Override
	public RuleApp completeBuiltInRuleApp(RuleApp app, Goal goal,
	        Services services) {
		if (mainWindow.getMediator().autoMode()) {
			return super.completeBuiltInRuleApp(
			        app, goal, services);
		}
		RuleApp result = app;
		if (app.rule() instanceof UseOperationContractRule) {
			Instantiation inst = UseOperationContractRule.computeInstantiation(
			        app.posInOccurrence().subTerm(), services);
			ImmutableSet<FunctionalOperationContract> contracts = UseOperationContractRule
			        .getApplicableContracts(
			                inst, services);
			FunctionalOperationContract[] contractsArr = contracts
			        .toArray(new FunctionalOperationContract[contracts.size()]);
			ContractConfigurator cc = new ContractConfigurator(
			        MainWindow.getInstance(), services, contractsArr,
			        "Contracts for " + inst.pm.getName(), true);
			if (cc.wasSuccessful()) {
				result = ((UseOperationContractRule) app.rule()).createApp(
				        app.posInOccurrence()).setContract(
				        cc.getContract());
			}
		} else if (app.rule() instanceof UseDependencyContractRule) {
			UseDependencyContractApp cApp = (UseDependencyContractApp) result;
			
			cApp = cApp.tryToInstantiateContract(services);	
			
			final List<PosInOccurrence> steps = 
					UseDependencyContractRule.
					 getSteps(cApp.posInOccurrence(), goal.sequent(), services);                
			PosInOccurrence step = letUserChooseStep(steps, services);
			if (step == null) {
				return null;
			}
			result = cApp.setStep(step);
		}
		return result.complete() ? result : null;
	}

	private static final class TermStringWrapper {
		final Term term;
		final String string;

		TermStringWrapper(Term term, String string) {
			this.term = term;
			this.string = string;
		}

		@Override
		public String toString() {
			return string;
		}
	}

   @Override
   public ProblemInitializer createProblemInitializer() {
      ProblemInitializer pi = new ProblemInitializer(this, 
                                                     mainWindow.getMediator().getProfile(), 
                                                     new Services(mainWindow.getMediator().getExceptionHandler()), 
                                                     true, 
                                                     this);
       return pi;
   }
}
