/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.smt;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javafx.animation.KeyFrame;
import javafx.animation.Timeline;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.paint.Color;
import javafx.stage.Window;
import javafx.util.Duration;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.colors.ColorPaletteF;
import de.uka.ilkd.key.gui.fx.colors.ColorSettingsF;
import de.uka.ilkd.key.gui.fx.smt.InformationWindowF.Information;
import de.uka.ilkd.key.gui.fx.smt.ProgressDialogF.ProgressCellF;
import de.uka.ilkd.key.gui.fx.smt.ProgressDialogF.ProgressRowF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings.ProgressMode;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTFocusResults;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Launches SMT solvers and presents their progress in the {@link ProgressDialogF},
 * counter-part of the Swing {@code de.uka.ilkd.key.gui.smt.SolverListener}. The listener is
 * called by the {@link SolverLauncher} on its background thread and posts every UI interaction
 * to the FX thread; a {@link Timeline} polls the solver states (the Swing original used a
 * {@code java.util.Timer} with the same task) and writes the progress, the remaining time and
 * the result coloring (green/red/orange/blue from the {@code [solverListener]} palette colors)
 * into the table cells.
 * <p>
 * KNOWN-SIMPLIFIED: the results are applied directly ({@code SMTRule} built-in rule application
 * with the unsat core if available) instead of through the Swing {@code SMTProofApplyUserAction}
 * history mechanism (no undo entry for the automatic CLOSE-mode application), and the input
 * freeze around the rule application is not available yet (the {@code stopInterface} P0
 * remainder).
 */
public class SolverListenerF implements SolverLauncherListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(SolverListenerF.class);

    /**
     * The progress bar resolution of one solver run (Swing {@code SolverListener.RESOLUTION}).
     */
    private static final int RESOLUTION = 1000;

    /** the poll interval of the dialog refresh (the Swing original polled every 10 ms) */
    private static final long POLL_MILLIS = 100;

    private static int FILE_ID = 0;

    private final DefaultSMTSettings settings;
    private final Proof smtProof;
    private final Window owner;
    private final KeYMediatorF mediator;

    /**
     * Every intern SMT problem refers to one solver.
     */
    private final List<InternSMTProblemF> problems = new ArrayList<>();

    private List<SMTProblem> smtProblems = new ArrayList<>();
    /** the table cells indexed by {@code [problemIndex][solverIndex]} */
    private List<List<ProgressCellF>> cellGrid = new ArrayList<>();
    private boolean[][] problemProcessed;
    private int finishedCounter;
    private Timeline timer;

    private ProgressDialogF progressDialog;

    /**
     * the currently visible progress dialog; used by the {@code key.fx.verify.smt} hook to
     * discard a dialog whose run did not complete (the dialog is application modal).
     */
    private static ProgressDialogF currentDialog;

    public SolverListenerF(DefaultSMTSettings settings, Proof smtProof, Window owner,
            KeYMediatorF mediator) {
        this.settings = settings;
        this.smtProof = smtProof;
        this.owner = owner;
        this.mediator = mediator;
    }

    /**
     * One solver run on one problem, counter-part of the Swing
     * {@code SolverListener.InternSMTProblem}: the table position, the timing and the
     * {@link Information} entries presented by the {@link InformationWindowF}.
     */
    public static final class InternSMTProblemF {
        final int problemIndex;
        final int solverIndex;
        final SMTProblem problem;
        final SMTSolver solver;
        private final List<Information> information = new ArrayList<>();
        private boolean stopped = false;
        private boolean running = false;

        private long timeToSolve;

        InternSMTProblemF(int problemIndex, int solverIndex, SMTProblem problem,
                SMTSolver solver) {
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

        public SMTSolver getSolver() {
            return solver;
        }

        public List<Information> getInformation() {
            return information;
        }

        private void addInformation(String title, String content) {
            information.add(new Information(title, content, solver.name()));
        }

        /**
         * Collects the per-solver information entries (Swing
         * {@code SolverListener.InternSMTProblem.createInformation}): the error message, the
         * SMT2 translation, the taclet translation, the solver output and the warnings.
         */
        public void createInformation() {
            if (solver.getException() != null) {
                StringWriter writer = new StringWriter();
                solver.getException().printStackTrace(new PrintWriter(writer));
                addInformation("Error-Message",
                    solver.getException().toString() + "\n\n" + writer);
            }
            addInformation("Solver Input", solver.getRawSolverInput());
            if (solver.getTacletTranslation() != null) {
                addInformation("Taclets", solver.getTacletTranslation().toString());
            }
            addInformation("Solver Output", solver.getRawSolverOutput());

            Collection<Throwable> exceptionsOfTacletTranslation =
                solver.getExceptionsOfTacletTranslation();
            if (!exceptionsOfTacletTranslation.isEmpty()) {
                StringBuilder exceptionText = new StringBuilder(
                    "The following exceptions have ocurred while translating the taclets:\n\n");
                int i = 1;
                for (Throwable e : exceptionsOfTacletTranslation) {
                    exceptionText.append(i).append(". ").append(e.getMessage());
                    StringWriter sw = new StringWriter();
                    PrintWriter pw = new PrintWriter(sw);
                    e.printStackTrace(pw);
                    exceptionText.append("\n\n").append(sw);
                    exceptionText.append("\n #######################\n\n");
                    i++;
                }
                addInformation("Warning", exceptionText.toString());
            }

            if (solver.getType().supportHasBeenChecked()
                    && !solver.getType().isSupportedVersion()) {
                addInformation("Solver Support", computeSolverTypeWarningMessage(solver.getType()));
            }
        }

        @Override
        public String toString() {
            return solver.name() + " applied on " + problem.getName();
        }

        String getTimeInSecAsString() {
            long intPart = timeToSolve / 1000;
            long decPart = timeToSolve % 1000;
            String decString = decPart >= 100 ? Long.toString(decPart)
                    : decPart >= 10 ? "0" + decPart : "00" + decPart;
            return intPart + "." + decString + "s";
        }

        void startTime() {
            if (!running) {
                timeToSolve = System.currentTimeMillis();
                running = true;
            }
        }

        void stopTime() {
            if (!stopped) {
                timeToSolve = System.currentTimeMillis() - timeToSolve;
                stopped = true;
            }
        }
    }

    /**
     * Runs the solver union on every open goal of the proof (Swing
     * {@code SMTInvokeAction.actionPerformed}, SMTInvokeAction.java:75-96): a background thread
     * builds the settings, the launcher with this listener and launches
     * {@code SMTProblem.createSMTProblems(proof)}.
     *
     * @param mediator the FX mediator (used by the Apply/Focus buttons)
     * @param owner the owner window of the progress dialog; may be {@code null}
     * @param proof the proof to run the solvers on
     * @param solverUnion the solvers/solver types to start
     */
    public static void launchOnProof(KeYMediatorF mediator, Window owner, Proof proof,
            SolverTypeCollection solverUnion) {
        launch(mediator, owner, proof, SMTProblem.createSMTProblems(proof),
            solverUnion.getTypes());
    }

    /**
     * Runs the solver union on the single given goal (Swing
     * {@code CurrentGoalViewMenu.SMTAction}, CurrentGoalViewMenu.java:765-790).
     *
     * @param mediator the FX mediator (used by the Apply/Focus buttons)
     * @param owner the owner window of the progress dialog; may be {@code null}
     * @param goal the goal whose sequent is translated
     * @param solverUnion the solvers/solver types to start
     */
    public static void launchOnGoal(KeYMediatorF mediator, Window owner, Goal goal,
            SolverTypeCollection solverUnion) {
        launch(mediator, owner, goal.proof(), List.of(new SMTProblem(goal)),
            solverUnion.getTypes());
    }

    /**
     * Builds the settings and the launcher with this listener and launches the given problems
     * (Swing SMTInvokeAction/CurrentGoalViewMenu.SMTAction launch bodies). The launch is
     * synchronous (it blocks until every solver finished) and runs in a daemon background
     * thread; the dialog is presented on the FX thread via the listener callbacks.
     *
     * @param mediator the FX mediator (used by the Apply/Focus buttons)
     * @param owner the owner window of the progress dialog; may be {@code null}
     * @param proof the proof the problems belong to
     * @param smtProblems the problems to translate and solve
     * @param solverTypes the solver types to run on each problem
     */
    public static void launch(KeYMediatorF mediator, Window owner, Proof proof,
            Collection<SMTProblem> smtProblems, Collection<SolverType> solverTypes) {
        Thread thread = new Thread(() -> {
            DefaultSMTSettings settings =
                new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                    proof.getSettings().getNewSMTSettings(), proof);
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(new SolverListenerF(settings, proof, owner, mediator));
            launcher.launch(solverTypes, smtProblems, proof.getServices());
        }, "SMTRunner");
        thread.setDaemon(true);
        thread.start();
    }

    @Override
    public void launcherStarted(Collection<SMTProblem> smtproblems,
            Collection<SolverType> solverTypes, SolverLauncher launcher) {
        // launch() is synchronous (it blocks the background thread until every solver finished),
        // so the dialog is always prepared before launcherStopped is posted to the FX thread
        // (FIFO queue) — the Swing original had the same ordering via invokeLater
        Platform.runLater(() -> prepareDialog(smtproblems, solverTypes, launcher));
    }

    @Override
    public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> problemSolvers) {
        Platform.runLater(() -> finish(launcher));
    }

    private void finish(SolverLauncher launcher) {
        stopTimer();
        storeInformation();
        progressDialog.setEditable();
        refreshDialog();
        progressDialog.setModus(ProgressDialogF.Modus.SOLVERS_DONE);
        for (InternSMTProblemF problem : problems) {
            problem.createInformation();
        }
        if (settings.getModeOfProgressDialog() == ProgressMode.CLOSE) {
            applyEvent(launcher);
        }
    }

    private void prepareDialog(Collection<SMTProblem> smtproblems,
            Collection<SolverType> solverTypes, SolverLauncher launcher) {
        this.smtProblems = new ArrayList<>(smtproblems);
        boolean ce = solverTypes.contains(SolverTypes.Z3_CE_SOLVER);

        List<String> titles = new ArrayList<>();
        titles.add("");
        ObservableList<ProgressRowF> rows = FXCollections.observableArrayList();
        problemProcessed = new boolean[solverTypes.size()][smtProblems.size()];

        int x = 0;
        for (SMTProblem problem : smtProblems) {
            List<SMTSolver> solvers = new ArrayList<>(problem.getSolvers());
            List<ProgressCellF> cells = new ArrayList<>();
            int y = 0;
            for (SMTSolver solver : solvers) {
                problems.add(new InternSMTProblemF(x, y, problem, solver));
                cells.add(new ProgressCellF());
                y++;
            }
            cellGrid.add(cells);
            rows.add(new ProgressRowF(problem.getName(), cells));
            x++;
        }
        for (SolverType type : solverTypes) {
            titles.add(type.getName());
        }

        progressDialog =
            new ProgressDialogF(owner, ce, RESOLUTION, smtProblems.size() * solverTypes.size(),
                titles, rows, createDialogListener(launcher, ce));
        currentDialog = progressDialog;
        progressDialog.setOverallProgress(0);
        progressDialog.show();
        startTimer();
    }

    private ProgressDialogF.Listener createDialogListener(SolverLauncher launcher, boolean ce) {
        return new ProgressDialogF.Listener() {
            @Override
            public void infoButtonClicked(int column, int row) {
                InternSMTProblemF problem = getProblem(column, row);
                if (problem != null) {
                    showInformation(problem);
                }
            }

            @Override
            public void stopButtonClicked() {
                stopEvent(launcher);
            }

            @Override
            public void applyButtonClicked() {
                applyEvent(launcher);
            }

            @Override
            public void discardButtonClicked() {
                discardEvent(launcher, ce);
            }

            @Override
            public void focusButtonClicked() {
                focusResults();
            }
        };
    }

    private InternSMTProblemF getProblem(int column, int row) {
        for (InternSMTProblemF problem : problems) {
            if (problem.problemIndex == row && problem.solverIndex == column) {
                return problem;
            }
        }
        return null;
    }

    private void startTimer() {
        timer = new Timeline(new KeyFrame(Duration.millis(POLL_MILLIS), e -> refreshDialog()));
        timer.setCycleCount(Timeline.INDEFINITE);
        timer.play();
    }

    private void stopTimer() {
        if (timer != null) {
            timer.stop();
            timer = null;
        }
    }

    private void refreshDialog() {
        for (InternSMTProblemF problem : problems) {
            refreshProgressOfProblem(problem);
        }
    }

    private void refreshProgressOfProblem(InternSMTProblemF problem) {
        switch (problem.solver.getState()) {
            case Running -> running(problem);
            case Stopped -> stopped(problem);
            case Waiting -> {
                // the solver has not been started yet (bounded process count)
            }
        }
    }

    private void running(InternSMTProblemF problem) {
        problem.startTime();
        long maxTime = problem.solver.getTimeout();
        long startTime = problem.solver.getStartTime();
        long currentTime = System.currentTimeMillis();
        long progress = RESOLUTION - ((startTime - currentTime) * RESOLUTION) / maxTime;
        cell(problem).progress.set((int) Math.min(Math.max(progress, 0), RESOLUTION));
        float remainingTime = Math.max((startTime - currentTime) / 100 / 10.0f, 0);
        cell(problem).text.set(remainingTime + " sec.");
    }

    private void stopped(InternSMTProblemF problem) {
        problem.stopTime();

        int x = problem.getSolverIndex();
        int y = problem.getProblemIndex();

        if (!problemProcessed[x][y]) {
            finishedCounter++;
            progressDialog.setOverallProgress(finishedCounter);
            problemProcessed[x][y] = true;
        }

        if (problem.solver.wasInterrupted()) {
            interrupted(problem);
        } else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
            successfullyStopped(problem);
        } else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE) {
            unsuccessfullyStopped(problem);
        } else {
            unknownStopped(problem);
        }
    }

    private void interrupted(InternSMTProblemF problem) {
        ReasonOfInterruption reason = problem.solver.getReasonOfInterruption();
        ProgressCellF cell = cell(problem);
        switch (reason) {
            case Exception -> {
                cell.progress.set(0);
                cell.textColor.set(colorOf(ColorPaletteF.SMT_RED));
                cell.text.set("Exception!");
            }
            case NoInterruption -> throw new RuntimeException("This position is not reachable!");
            case Timeout -> {
                cell.progress.set(0);
                cell.text.set("Timeout.");
            }
            case User -> cell.text.set("Interrupted by user.");
        }
    }

    private void successfullyStopped(InternSMTProblemF problem) {
        String timeInfo = " (" + problem.getTimeInSecAsString() + ")";
        ProgressCellF cell = cell(problem);
        cell.progress.set(0);
        cell.textColor.set(colorOf(ColorPaletteF.SMT_GREEN));
        if (problem.solver.getType() == SolverTypes.Z3_CE_SOLVER) {
            cell.text.set("No Counterexample.");
        } else {
            cell.text.set("Valid" + timeInfo);
        }
    }

    private void unsuccessfullyStopped(InternSMTProblemF problem) {
        String timeInfo = " (" + problem.getTimeInSecAsString() + ")";
        ProgressCellF cell = cell(problem);
        cell.progress.set(0);
        if (problem.solver.getType() == SolverTypes.Z3_CE_SOLVER) {
            cell.textColor.set(colorOf(ColorPaletteF.SMT_RED));
            cell.text.set("Counter Example" + timeInfo);
        } else {
            cell.textColor.set(Color.rgb(200, 150, 0));
            cell.text.set("Possible Counter Example" + timeInfo);
        }
    }

    private void unknownStopped(InternSMTProblemF problem) {
        ProgressCellF cell = cell(problem);
        cell.progress.set(0);
        cell.textColor.set(Color.BLUE);
        cell.text.set("Unknown.");
    }

    private ProgressCellF cell(InternSMTProblemF problem) {
        return cellGrid.get(problem.problemIndex).get(problem.solverIndex);
    }

    /**
     * Applies the results (Swing {@code SolverListener.applyResults}): every goal whose solver
     * returned a valid result is closed with the {@code SMTRule} built-in rule application (with
     * the unsat core if the solver provided one). The Swing original wraps this in a
     * {@code SMTProofApplyUserAction} (undoable); the FX port applies directly.
     */
    private void applyResults() {
        Set<Goal> goalsClosed = new HashSet<>();
        for (InternSMTProblemF problem : problems) {
            Goal goal = problem.problem.getGoal();
            if (goalsClosed.contains(goal)
                    || problem.solver.getFinalResult().isValid() != ThreeValuedTruth.VALID) {
                continue;
            }
            goalsClosed.add(goal);
            ImmutableList<PosInOccurrence> unsatCore =
                SMTFocusResults.getUnsatCore(problem.problem);
            IBuiltInRuleApp app;
            if (unsatCore != null) {
                app = SMTRule.INSTANCE.createApp(problem.solver.name(), unsatCore);
            } else {
                app = SMTRule.INSTANCE.createApp(problem.solver.name());
            }
            app = AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, false);
            if (app == null) {
                // should be unreachable under normal circumstances
                throw new RuntimeException("Could not instantiate SMT Rule Application");
            }
            goal.apply(app);
        }
        // switch to new open goal (Swing: mediator.getSelectionModel().defaultSelection();
        // the mediator.stopInterface/startInterface input freeze is not ported yet)
        mediator.getSelectionModel().defaultSelection();
    }

    /**
     * Reduce the sequent on each open goal to the formulas present in the unsat core computed
     * by one of the SMT solvers (Swing {@code SolverListener.focusResults}).
     */
    private void focusResults() {
        Set<Goal> focusedGoals = new HashSet<>();
        Set<Goal> failedToFocus = new HashSet<>();
        for (InternSMTProblemF problem : problems) {
            Goal goal = problem.problem.getGoal();
            Node goalNode = goal.node();
            if (focusedGoals.contains(goal)
                    || problem.solver.getFinalResult().isValid() != ThreeValuedTruth.VALID) {
                continue; // already done
            }
            if (SMTFocusResults.focus(problem.problem, mediator.getServices())) {
                focusedGoals.add(goal);
                failedToFocus.remove(goal);

                // focus SMT application
                if (goalNode == mediator.getSelectedNode()) {
                    mediator.getSelectionModel().setSelectedNode(goal.node());
                }
            } else {
                failedToFocus.add(goal);
            }
        }
        if (!failedToFocus.isEmpty()) {
            Alert alert = new Alert(AlertType.ERROR,
                "None of the SMT solvers provided an unsat core for one of the goals.",
                ButtonType.OK);
            alert.setTitle("Failed to use unsat core");
            alert.setHeaderText(null);
            if (owner != null) {
                alert.initOwner(owner);
            }
            alert.show();
        }
    }

    private void showInformation(InternSMTProblemF problem) {
        InformationWindowF.show(owner, "Information for " + problem, problem.getInformation());
    }

    private void stopEvent(SolverLauncher launcher) {
        launcher.stop();
    }

    private void discardEvent(SolverLauncher launcher, boolean counterexample) {
        launcher.stop();
        progressDialog.close();
        currentDialog = null;
        // remove semantics blasting proof for ce dialog
        if (counterexample && smtProof != null) {
            smtProof.dispose();
        }
    }

    private void applyEvent(SolverLauncher launcher) {
        launcher.stop();
        applyResults();
        /*
         * Previously, the progressDialog was only made invisible which enabled users to click
         * the apply button more than once, each time creating a new SMT goal. Disposing of the
         * dialog is fine as it is created anew each time a SolverLauncher is started anyway
         * (see #launcherStarted(), #prepareDialog()). (comment preserved from Swing)
         */
        progressDialog.close();
        currentDialog = null;
    }

    /**
     * Discards the currently visible progress dialog, if any ({@code key.fx.verify.smt} hook:
     * a run that did not complete would otherwise leave the application-modal dialog blocking
     * the UI).
     */
    public static void discardCurrentDialog() {
        ProgressDialogF dialog = currentDialog;
        if (dialog != null) {
            dialog.close();
            currentDialog = null;
        }
    }

    private void storeInformation() {
        if (settings.storeSMTTranslationToFile()
                || (settings.makesUseOfTaclets() && settings.storeTacletTranslationToFile())) {
            for (InternSMTProblemF problem : problems) {
                storeInformation(problem.getProblem());
            }
        }
    }

    private void storeInformation(SMTProblem problem) {
        for (SMTSolver solver : problem.getSolvers()) {
            if (settings.storeSMTTranslationToFile()) {
                storeSMTTranslation(solver, problem.getGoal(), solver.getTranslation());
            }
            if (settings.makesUseOfTaclets() && settings.storeTacletTranslationToFile()
                    && solver.getTacletTranslation() != null) {
                storeTacletTranslation(solver, problem.getGoal(), solver.getTacletTranslation());
            }
        }
    }

    private void storeTacletTranslation(SMTSolver solver, Goal goal,
            TacletSetTranslation translation) {
        String path = settings.getPathForTacletTranslation();
        path = finalizePath(path, solver, goal);
        storeToFile(translation.toString(), path);
    }

    private void storeSMTTranslation(SMTSolver solver, Goal goal, String problemString) {
        String path = settings.getPathForSMTTranslation();

        String fileName =
            goal.proof().name() + "_" + goal.getTime() + "_" + solver.name() + ".smt";
        path = path + File.separator + fileName;
        path = finalizePath(path, solver, goal);
        storeToFile(problemString, path);
    }

    private void storeToFile(String text, String path) {
        try {
            final BufferedWriter out2 =
                new BufferedWriter(new FileWriter(path, StandardCharsets.UTF_8));
            out2.write(text);
            out2.close();
        } catch (IOException e) {
            throw new RuntimeException("Could not store to file " + path + ".", e);
        }
    }

    private String finalizePath(String path, SMTSolver solver, Goal goal) {
        Calendar c = Calendar.getInstance();
        String date =
            c.get(Calendar.YEAR) + "-" + c.get(Calendar.MONTH) + "-" + c.get(Calendar.DATE);
        String time = c.get(Calendar.HOUR_OF_DAY) + "-" + c.get(Calendar.MINUTE) + "-"
            + c.get(Calendar.SECOND);

        path = path.replaceAll("%d", date);
        path = path.replaceAll("%s", solver.name());
        path = path.replaceAll("%t", time);
        path = path.replaceAll("%i", Integer.toString(FILE_ID++));
        path = path.replaceAll("%g", Integer.toString(goal.node().serialNr()));

        return path;
    }

    /**
     * @return the current theme's color of a palette property (the Swing
     *         {@code ColorSettings.ColorProperty.get()} of the active theme)
     */
    private static Color colorOf(ColorSettingsF.ColorPropertyF property) {
        return ThemeManager.getInstance().themeProperty().get() == Theme.DARK
                ? property.getDarkValue()
                : property.getLightValue();
    }

    /**
     * @return the warning message of an unsupported solver version (Swing
     *         {@code SolverListener.computeSolverTypeWarningMessage})
     */
    public static String computeSolverTypeWarningMessage(SolverType type) {
        return ("""
                You are using a version of %s which has not been tested for this version of KeY.
                It can therefore be that errors occur that would not occur
                using the following version or higher:
                %s""").formatted(type.getName(), type.getMinimumSupportedVersion());
    }

    /**
     * Checks if the given {@link JTerm} contains a modality, query, or update (Swing
     * {@code SolverListener.containsModalityOrQuery}).
     *
     * @param term the term to check
     * @return {@code true} contains at least one modality or query
     */
    public static boolean containsModalityOrQuery(JTerm term) {
        ContainsModalityOrQueryVisitor visitor = new ContainsModalityOrQueryVisitor();
        term.execPostOrder(visitor);
        return visitor.containsModOrQuery();
    }

    /**
     * Utility class used to check whether a term contains constructs that are not handled by the
     * SMT translation (port of the Swing
     * {@code SolverListener.ContainsModalityOrQueryVisitor}).
     */
    protected static class ContainsModalityOrQueryVisitor implements DefaultVisitor {

        boolean containsModQuery = false;

        @Override
        public void visit(Term visited) {
            if (visited.op() instanceof JModality || visited.op() instanceof IProgramMethod) {
                containsModQuery = true;
            }
        }

        public boolean containsModOrQuery() {
            return containsModQuery;
        }
    }
}
