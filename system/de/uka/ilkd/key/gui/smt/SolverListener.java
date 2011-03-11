package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.awt.event.WindowStateListener;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Calendar;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Timer;
import java.util.TimerTask;

import javax.swing.JFrame;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.smt.InformationWindow.Information;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.taclettranslation.TacletSetTranslation;

public class SolverListener implements SolverLauncherListener {
    private ProgressDialog progressDialog;
    private ProgressPanel[] progressPanels;
    // Every intern SMT problem refers to one solver
    private Collection<InternSMTProblem> problems = new LinkedList<InternSMTProblem>();
    // Every SMT problem refers to many solvers.
    private Collection<SMTProblem> smtProblems = new LinkedList<SMTProblem>();
    private Timer timer = new Timer();
    private final static Color RED = new Color(180, 43, 43);
    private final static Color GREEN = new Color(43, 180, 43);
    private static int FILE_ID = 0;

    private static final int RESOLUTION = 1000;
    
 

    private class InternSMTProblem {
	final int problemIndex;
	final int solverIndex;
	final SMTSolver solver;
	final SMTProblem problem;

	public InternSMTProblem(int problemIndex, int solverIndex,
	        SMTProblem problem, SMTSolver solver) {
	    super();
	    this.problemIndex = problemIndex;
	    this.solverIndex = solverIndex;
	    this.problem = problem;
	    this.solver = solver;
	}

	public int getSolverIndex() {
	    return solverIndex;
	}

	public int getProblemIndex() {
	    return problemIndex;
	}

	public SMTProblem getProblem() {
	    return problem;
	}

    }
    

    @Override
    public void launcherStopped(SolverLauncher launcher,
	    Collection<SMTSolver> problemSolvers) {
	timer.cancel();
	refreshDialog();
	progressDialog.setStopButtonEnabled(false);
	storeInformation();

	for (InternSMTProblem problem : problems) {
	    int problemIndex = problem.getProblemIndex();
	    getPanel(problem).addInformation(
		    problemIndex,
		    new Information("Translation", problem.solver
		            .getTranslation()));
	    if (problem.solver.getTacletTranslation() != null) {
		getPanel(problem).addInformation(
		        problemIndex,
		        new Information("Taclets", problem.solver
		                .getTacletTranslation().toString()));
	    }
	    if (problem.solver.getException() != null) {
		getPanel(problem).addInformation(
		        problemIndex,
		        new Information("Error-Message", problem.solver
		                .getException().toString()));
	    }
	}

    }

    private String getTitle(SMTProblem p) {
	String title = "";
	Iterator<SMTSolver> it = p.getSolvers().iterator();
	while (it.hasNext()) {
	    title += it.next().name();
	    if (it.hasNext()) {
		title += ", ";
	    }
	}
	return title;
    }

    private void applyResults() {
	for (SMTProblem problem : smtProblems) {
	    if (problem.getFinalResult().isValid() == ThreeValuedTruth.TRUE) {
		problem.getGoal().apply(
		        new RuleAppSMT(problem.getGoal(), getTitle(problem)));
	    }
	}

    }

    private void prepareDialog(Collection<SMTProblem> smtproblems,
	    Collection<SolverType> solverTypes, final SolverLauncher launcher) {
	this.smtProblems = smtproblems;
	progressPanels = new ProgressPanel[solverTypes.size()];
	String names[] = new String[smtproblems.size()];
	int x = 0;
	for (SMTProblem problem : smtproblems) {
	    int y = 0;
	    for (SMTSolver solver : problem.getSolvers()) {
		this.problems.add(new InternSMTProblem(x, y, problem, solver));
		y++;
	    }
	    names[x] = problem.getName();
	    x++;
	}

	int i = 0;
	for (SolverType factory : solverTypes) {
	    progressPanels[i] = new ProgressPanel(factory.getName(),
		    smtproblems.size(), RESOLUTION, names);
	    i++;
	}

	progressDialog = new ProgressDialog(progressPanels,
	        new ActionListener() {

		    @Override
		    public void actionPerformed(ActionEvent e) {
		        discardEvent(launcher);
		  
		    }
	        }, new ActionListener() {

		    @Override
		    public void actionPerformed(ActionEvent e) {
			
		
		        applyEvent(launcher);
		    
		    }
	        }, new ActionListener() {
		    @Override
		    public void actionPerformed(ActionEvent e) {
		        stopEvent(launcher);
		    }
	        });

	SwingUtilities.invokeLater(new Runnable() {
	    
	    @Override
	    public void run() {
		progressDialog.setVisible(true);
		
	    }
	});


    }
    


    private void stopEvent(final SolverLauncher launcher) {
	launcher.stop();
    }

    private void discardEvent(final SolverLauncher launcher) {
	launcher.stop();
	progressDialog.setVisible(false);
    }

    private void applyEvent(final SolverLauncher launcher) {
	launcher.stop();
	applyResults();
	progressDialog.setVisible(false);
    }

    @Override
    public void launcherStarted(final Collection<SMTProblem> smtproblems,
	    final Collection<SolverType> solverTypes,
	    final SolverLauncher launcher) {
	prepareDialog(smtproblems, solverTypes, launcher);

	timer.schedule(new TimerTask() {
	    @Override
	    public void run() {
		refreshDialog();
	    }
	}, 0, 10);
    }


    private void refreshDialog() {
	for (InternSMTProblem problem : problems) {
	    refreshProgessOfProblem(problem);
	}
    }

    private long calculateProgress(InternSMTProblem problem) {
	long maxTime = problem.solver.getTimeout();
	long startTime = problem.solver.getStartTime();
	long currentTime = System.currentTimeMillis();

	return RESOLUTION - ((startTime - currentTime) * RESOLUTION) / maxTime;
    }

    private float calculateRemainingTime(InternSMTProblem problem) {
	long startTime = problem.solver.getStartTime();
	long currentTime = System.currentTimeMillis();
	long temp = (startTime - currentTime) / 100;
	return Math.max((float) temp / 10.0f, 0);
    }

    private ProgressPanel getPanel(InternSMTProblem problem) {

	return progressPanels[problem.getSolverIndex()];

    }

    private boolean refreshProgessOfProblem(InternSMTProblem problem) {
	SolverState state = problem.solver.getState();
	switch (state) {
	case Running:
	    running(problem);
	    return true;
	case Stopped:
	    stopped(problem);
	    return false;
	case Waiting:
	    waiting(problem);
	    return true;

	}
	return true;

    }

    private void waiting(InternSMTProblem problem) {

    }

    private void running(InternSMTProblem problem) {
	int problemIndex = problem.getProblemIndex();
	long progress = calculateProgress(problem);
	getPanel(problem).setProgress(problemIndex, (int) progress);
	float remainingTime = calculateRemainingTime(problem);
	getPanel(problem).setText(problemIndex,
	        Float.toString(remainingTime) + " sec.");
    }

    private void stopped(InternSMTProblem problem) {
	if (problem.solver.wasInterrupted()) {
	    interrupted(problem);
	} else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.TRUE) {
	    successfullyStopped(problem);
	} else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE) {
	    unsuccessfullyStopped(problem);
	} else {
	    unknownStopped(problem);
	}
    }

    private void interrupted(InternSMTProblem problem) {
	int problemIndex = problem.getProblemIndex();
	ReasonOfInterruption reason = problem.solver.getReasonOfInterruption();
	switch (reason) {
	case Exception:
	    progressDialog.setInfo("Exception!");
	    progressDialog.setInfoColor(RED);
	    getPanel(problem).setProgress(problemIndex, 0);
	    getPanel(problem).setColor(problemIndex, RED);
	    getPanel(problem).setText(problemIndex, "Exception.");

	    break;
	case NoInterruption:
	    throw new RuntimeException("This position should not be reachable!");

	case Timeout:
	    getPanel(problem).setProgress(problemIndex, RESOLUTION);
	    getPanel(problem).setText(problemIndex, "Timeout.");
	    break;
	case User:
	    getPanel(problem).setText(problemIndex, "Interrupted by user.");
	    break;
	}
    }

    private void successfullyStopped(InternSMTProblem problem) {
	int problemIndex = problem.getProblemIndex();
	getPanel(problem).setProgress(problemIndex, 0);
	getPanel(problem).setColor(problemIndex, GREEN);
	getPanel(problem).setText(problemIndex, "Valid.");
    }

    private void unsuccessfullyStopped(InternSMTProblem problem) {
	int problemIndex = problem.getProblemIndex();
	getPanel(problem).setProgress(problemIndex, 0);
	getPanel(problem).setColor(problemIndex, RED);
	getPanel(problem).setText(problemIndex, "Falsifiable.");

    }

    private void unknownStopped(InternSMTProblem problem) {
	int problemIndex = problem.getProblemIndex();
	getPanel(problem).setText(problemIndex, "Unknown.");
    }

    private void storeInformation() {
	SMTSettings settings = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
	if (settings.storeSMTTranslationToFile()
	        || (settings.makesUseOfTaclets() && settings
	                .storeTacletTranslationToFile())) {
	    for (InternSMTProblem problem : problems) {
		storeInformation(problem.getProblem(), settings);
	    }
	}

    }

    private void storeInformation(SMTProblem problem, SMTSettings settings) {
	for (SMTSolver solver : problem.getSolvers()) {
	    if (settings.storeSMTTranslationToFile()) {
		storeSMTTranslation(solver, problem.getGoal(), solver
		        .getTranslation(), settings);
	    }
	    if (settings.makesUseOfTaclets()
		    && settings.storeTacletTranslationToFile()
		    && solver.getTacletTranslation() != null) {
		storeTacletTranslation(solver, problem.getGoal(), solver
		        .getTacletTranslation());
	    }
	}
    }

    private void storeTacletTranslation(SMTSolver solver, Goal goal,
	    TacletSetTranslation translation) {
	String path = ProofSettings.DEFAULT_SETTINGS.getSMTSettings()
	        .getPathForTacletTranslation();
	path = finalizePath(path, solver, goal);
	storeToFile(translation.toString(), path);
    }

    private void storeSMTTranslation(SMTSolver solver, Goal goal,
	    String problemString, SMTSettings settings) {
	String path = ProofSettings.DEFAULT_SETTINGS.getSMTSettings()
	        .getPathForSMTTranslation();
	path = finalizePath(path, solver, goal);
	storeToFile(problemString, path);

    }

    private void storeToFile(String text, String path) {
	try {
	    final BufferedWriter out2 = new BufferedWriter(new FileWriter(path));
	    out2.write(text);
	    out2.close();
	} catch (IOException e) {
	    throw new RuntimeException("Could not store to file " + path + ".");
	}
    }

    private String finalizePath(String path, SMTSolver solver, Goal goal) {
	Calendar c = Calendar.getInstance();
	String date = c.get(Calendar.YEAR) + "-" + c.get(Calendar.MONTH) + "-"
	        + c.get(Calendar.DATE);
	String time = c.get(Calendar.HOUR_OF_DAY) + "-"
	        + c.get(Calendar.MINUTE) + "-" + c.get(Calendar.SECOND);

	path = path.replaceAll("%d", date);
	path = path.replaceAll("%s", solver.name());
	path = path.replaceAll("%t", time);
	path = path.replaceAll("%i", Integer.toString(FILE_ID++));
	path = path.replaceAll("%g", Integer.toString(goal.node().serialNr()));

	return path;
    }

}
