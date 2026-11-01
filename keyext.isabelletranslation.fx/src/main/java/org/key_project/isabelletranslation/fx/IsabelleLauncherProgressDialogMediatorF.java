/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.text.DecimalFormat;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;
import javafx.stage.Window;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleLauncherListener;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.automation.IsabelleResult;
import org.key_project.isabelletranslation.automation.IsabelleRule;
import org.key_project.isabelletranslation.automation.IsabelleSolver;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Updates the {@link IsabelleSolverProgressDialogF} for a given {@link IsabelleLauncher}, JavaFX
 * port of
 * {@code org.key_project.isabelletranslation.gui.controller.IsabelleLauncherProgressDialogMediator}
 * (IsabelleLauncherProgressDialogMediator.java): a 10 ms refresh timer maps the solver states
 * (Preparing / Parsing / Running / Stopped) and the final results (valid / exception / timeout /
 * interrupted / unknown) onto the progress dialog; the Stop button interrupts the launcher, the
 * Apply button closes the goals whose solver found a proof and the Info button shows the theory
 * and the raw solver output (the Swing {@code InformationWindow}, shown through the
 * {@link IsabelleTranslationDialogF} port).
 * <p>
 * All dialog mutations are marshalled onto the JavaFX thread (the Swing original repaints from
 * the timer thread); the apply step closes the solved goals directly instead of through the
 * Swing {@code UserAction} machinery — the FX mediator API has no user-action seam, so the
 * application is not undoable (KNOWN-SIMPLIFIED, see key.ui.fx/KNOWN-SIMPLIFIED.md).
 */
@NullMarked
final class IsabelleLauncherProgressDialogMediatorF implements IsabelleLauncherListener {

    private static final Logger LOGGER =
        LoggerFactory.getLogger(IsabelleLauncherProgressDialogMediatorF.class);

    /**
     * The format used to display the remaining time for solver instances (Swing
     * remainingTimeFormat).
     */
    private static final DecimalFormat REMAINING_TIME_FORMAT = new DecimalFormat("#.#");

    /**
     * Timer used to schedule periodic refreshes of the Isabelle dialog (daemon, so a forgotten
     * cancel can never block the JVM shutdown).
     */
    private final Timer timer = new Timer("IsabelleLauncherTimerF", true);

    /** Indicates whether a user initiated stop has occurred (Swing userStopFlag). */
    private boolean userStopFlag = false;

    /** The proof which the launcher is working on; used to close solved goals. */
    private final Proof proof;

    /** The owner window of the progress dialog, may be {@code null}. */
    private final @Nullable Window owner;

    /** The launcher used in conjunction with the dialog. */
    private final IsabelleLauncher launcher;

    /** The number of finished instances (Swing finishedCounter). */
    private int finishedCounter = 0;

    /** The solvers started by the launcher (Swing solvers). */
    private List<IsabelleSolver> solvers = List.of();

    /** Stores which solvers have processed their problem (Swing finishedSolvers). */
    private boolean[][] finishedSolvers = new boolean[1][0];

    /** The dialog used; created on the FX thread in {@link #launcherStarted}. */
    private @Nullable IsabelleSolverProgressDialogF dialog;

    /** The last overall progress text set (verify harness seam). */
    private String overallText = "";

    /**
     * Creates a new mediator for the given proof and launcher (Swing constructor).
     *
     * @param owner the owner window of the progress dialog, may be {@code null}
     * @param proof the proof the launcher is working on
     * @param launcher the launcher used
     */
    IsabelleLauncherProgressDialogMediatorF(@Nullable Window owner, Proof proof,
            IsabelleLauncher launcher) {
        this.owner = owner;
        this.proof = proof;
        this.launcher = launcher;
    }

    @Override
    public void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers) {
        prepareDialog(solvers);

        FxUtil.runLater(() -> setProgressText(-1));
        timer.schedule(new TimerTask() {
            @Override
            public void run() {
                refreshDialog();
            }
        }, 0, 10);
    }

    @Override
    public void launcherPreparationFinished(IsabelleLauncher launcher,
            Collection<IsabelleSolver> solvers) {
        FxUtil.runLater(() -> setProgressText(0));
    }

    @Override
    public void launcherStopped(IsabelleLauncher launcher,
            Collection<IsabelleSolver> finishedInstances) {
        timer.cancel();

        FxUtil.runLater(() -> {
            if (dialog != null) {
                setProgressText(finishedInstances.size());
                dialog.setInfoEnabled(true);
                dialog.setModus(IsabelleSolverProgressDialogF.Modus.SOLVERS_DONE);
            }
        });
    }

    /**
     * The event that occurs after the stop button has been pressed in the dialog. Uses
     * {@link IsabelleLauncher#stopAll()} to interrupt the launcher (Swing stopEvent). Also sets
     * the userStopFlag so solver interrupts can be allocated to the user.
     */
    void stopEvent() {
        userStopFlag = true;
        launcher.stopAll();
    }

    /**
     * The event that occurs after the apply button has been pressed in the dialog. Invokes
     * {@link #applyResults()} to close solved goals (Swing applyEvent) and disposes of the
     * dialog. Must be called on the JavaFX thread (the apply button action runs there).
     */
    void applyEvent() {
        applyResults();
        closeDialog();
    }

    /**
     * The event that occurs after the discard button was pressed. Disposes of the dialog and does
     * nothing else (Swing discardEvent); the button is only available once the launcher has
     * stopped.
     */
    void discardEvent() {
        timer.cancel();
        closeDialog();
    }

    private void closeDialog() {
        FxUtil.runLater(() -> {
            if (dialog != null) {
                dialog.close();
                dialog = null;
            }
        });
    }

    /**
     * Closes the solved goals (Swing {@code applyResults} + IsabelleProofApplyUserAction.apply):
     * for every solver that found a proof, the Isabelle rule application with the successful
     * tactic is applied to the problem's goal. KNOWN-SIMPLIFIED: no user-action undo (the FX
     * mediator has no user-action seam, see the class documentation).
     */
    private void applyResults() {
        for (IsabelleSolver solver : solvers) {
            IsabelleResult result = solver.getFinalResult();
            if (result == null || !result.isSuccessful()) {
                continue;
            }
            IsabelleProblem problem = solver.getProblem();
            Goal goal = problem.getGoal();
            if (goal == null || goal.proof() != proof) {
                LOGGER.warn("Solver {} result refers to a goal outside the launched proof",
                    solver.name());
                continue;
            }
            try {
                var app = IsabelleRule.INSTANCE.createApp(solver.name(),
                    result.getSuccessfulTactic());
                app.tryToInstantiate(goal);
                goal.apply(app);
            } catch (Exception e) {
                LOGGER.error("Exception during application of Isabelle results", e);
            }
        }
    }

    /**
     * Prepares the dialog. Opens the dialog. Assigns the goal names of all solvers (Swing
     * prepareDialog: one caption per solver).
     *
     * @param solverCollection the solvers to be started by the launcher
     */
    private void prepareDialog(Collection<IsabelleSolver> solverCollection) {
        this.solvers = List.copyOf(solverCollection);
        List<String> captions = new ArrayList<>();
        for (IsabelleSolver solver : this.solvers) {
            captions.add(solver.getProblem().getName());
        }
        finishedSolvers = new boolean[1][this.solvers.size()];
        FxUtil.runAndWait(() -> {
            IsabelleSolverProgressDialogF d =
                new IsabelleSolverProgressDialogF(owner, captions, new DialogListenerF());
            d.show();
            dialog = d;
        });
    }

    /**
     * Refreshes the progress of all solvers (Swing refreshDialog). Called from the timer thread;
     * the dialog updates are marshalled onto the FX thread.
     */
    void refreshDialog() {
        FxUtil.runLater(() -> {
            if (dialog == null) {
                return;
            }
            for (IsabelleSolver solver : solvers) {
                refreshProgressOfSolver(solver);
            }
        });
    }

    /**
     * Refreshes the progress of a given solver by calling the requisite method in this class
     * (Swing refreshProgressOfSolver). Must be called on the FX thread.
     */
    private void refreshProgressOfSolver(IsabelleSolver solver) {
        IsabelleSolver.SolverState state = solver.getState();
        int row = solver.getSolverIndex();
        switch (state) {
            case Preparing -> preparing(row);
            case Parsing -> parsing(solver, row);
            case Running -> running(solver, row);
            case Stopped -> stopped(solver, row);
            case Waiting -> {
                // Swing waiting(): no-op
            }
        }
    }

    /**
     * Updates the progress bar for a solver which is currently parsing the Isabelle theory for
     * its problem (Swing parsing).
     */
    private void parsing(IsabelleSolver solver, int row) {
        if (dialog != null) {
            dialog.setRowText(row, "Parsing...", null);
        }
    }

    /**
     * Updates the progress bar of a solver that is currently preparing (Swing preparing).
     */
    private void preparing(int row) {
        if (dialog != null) {
            dialog.setRowText(row, "Preparing...", null);
        }
    }

    /**
     * Updates the dialog for a running solver: progress bar and remaining time (Swing running).
     */
    private void running(IsabelleSolver solver, int row) {
        if (dialog == null) {
            return;
        }
        long progress = calculateProgress(solver);
        dialog.setRowProgress(row, (int) progress);

        float remainingTime = calculateRemainingTime(solver);
        dialog.setRowText(row, REMAINING_TIME_FORMAT.format(remainingTime) + " sec.", null);
    }

    /**
     * Calculates the amount of progress made as a product of the percentage of the time passed
     * in comparison to the timeout duration of the solver and the resolution of the progress bar
     * (Swing calculateProgress).
     */
    private long calculateProgress(IsabelleSolver solver) {
        Duration maxDuration = Duration.ofSeconds(solver.getTimeout());
        Instant startTime = solver.getStartTime();

        return (long) Math.floor(IsabelleSolverProgressDialogF.RESOLUTION
                * (Duration.between(startTime, Instant.now()).toMillis()
                        / (double) maxDuration.toMillis()));
    }

    /**
     * Calculates the time remaining until the timeout of the solver (Swing
     * calculateRemainingTime).
     */
    private float calculateRemainingTime(IsabelleSolver solver) {
        Instant timeoutTime = solver.getStartTime().plusSeconds(solver.getTimeout());
        return Duration.between(Instant.now(), timeoutTime).toMillis() / 1000f;
    }

    /**
     * Updates the dialog for a stopped solver depending on its result (Swing stopped).
     */
    private void stopped(IsabelleSolver solver, int row) {
        if (dialog == null) {
            return;
        }
        if (!finishedSolvers[0][row]) {
            finishedCounter++;
            dialog.setProgress(finishedCounter);
            setProgressText(finishedCounter);
            finishedSolvers[0][row] = true;
        }

        IsabelleResult result = solver.getFinalResult();
        if (result == null) {
            unknownStopped(row);
            return;
        }

        switch (result.getType()) {
            case INTERRUPTED -> interrupted(row);
            case SUCCESS -> successfullyStopped(solver, row);
            case ERROR -> encounteredError(row);
            case TIMEOUT -> timedOut(row);
            default -> unknownStopped(row);
        }
    }

    /**
     * Updates the dialog for an interrupted solver (Swing interrupted).
     */
    private void interrupted(int row) {
        if (userStopFlag) {
            dialog.setRowProgress(row, 0);
            dialog.setRowText(row, "Interrupted by user.", null);
        } else {
            throw new RuntimeException("Solver was interrupted for unknown reasons!");
        }
    }

    /**
     * Updates the dialog for a solver that stopped successfully (Swing successfullyStopped).
     */
    private void successfullyStopped(IsabelleSolver solver, int row) {
        dialog.setRowProgress(row, 0);
        dialog.setRowText(row, "Valid ("
            + (solver.getComputationTime().toMillis() / 1000d) + "s)",
            IsabelleSolverProgressDialogF.GREEN);
    }

    /**
     * Updates the dialog for a solver that encountered an error (Swing encounteredError).
     */
    private void encounteredError(int row) {
        dialog.setRowProgress(row, 0);
        dialog.setRowText(row, "Exception!", IsabelleSolverProgressDialogF.RED);
    }

    /**
     * Updates the dialog for a solver that timed out (Swing timedOut).
     */
    private void timedOut(int row) {
        dialog.setRowProgress(row, 0);
        dialog.setRowText(row, "Timeout.", null);
    }

    /**
     * Updates the dialog for a solver that stopped for unknown reasons (Swing unknownStopped).
     */
    private void unknownStopped(int row) {
        dialog.setRowProgress(row, 0);
        dialog.setRowText(row, "Unknown.", IsabelleSolverProgressDialogF.UNKNOWN);
    }

    /**
     * Sets the progress text based on the number of solver instances that have processed their
     * problem. A negative value indicates the launcher is still preparing (Swing
     * setProgressText). Must be called on the FX thread.
     */
    private void setProgressText(int value) {
        if (dialog == null) {
            return;
        }
        if (value < 0) {
            overallText = "Preparing... (this might take a few seconds)";
        } else {
            overallText = "Processed " + value + " of " + solvers.size() + " problems.";
        }
        dialog.setOverallText(overallText);
    }

    /**
     * Shows the theory and the raw solver output of a solver (Swing
     * {@code showInformation} + InformationWindow): one tab with the translation theory, one tab
     * with the raw solver output or the exception.
     */
    private void showInformation(IsabelleSolver solver) {
        String informationTitle = solver.name() + ": " + solver.getProblem().getName();
        List<IsabelleTranslationDialogF.Entry> information = new ArrayList<>();
        information.add(new IsabelleTranslationDialogF.Entry("Translation theory", null,
            solver.getRawSolverInput(), null));
        if (solver.getFinalResult() != null && solver.getFinalResult().isError()) {
            information.add(new IsabelleTranslationDialogF.Entry("Exception", null, null,
                solver.getFinalResult().getException().getMessage()));
        } else {
            information.add(new IsabelleTranslationDialogF.Entry("Raw Solver Output", null,
                solver.getRawSolverOutput(), null));
        }
        FxUtil.runLater(() -> IsabelleTranslationDialogF.show(owner,
            "Information for " + informationTitle, information));
    }

    /**
     * Naive implementation of a dialog listener to react to button inputs by the user (Swing
     * IsabelleProgressDialogListenerImpl). The button actions arrive on the FX thread.
     */
    private class DialogListenerF implements IsabelleSolverProgressDialogF.Listener {
        @Override
        public void infoButtonClicked(int row) {
            IsabelleSolver solver = getSolver(row);
            if (solver == null) {
                throw new RuntimeException("Something went wrong in Dialog");
            }
            showInformation(solver);
        }

        @Override
        public void stopButtonClicked() {
            stopEvent();
        }

        @Override
        public void applyButtonClicked() {
            applyEvent();
        }

        @Override
        public void discardButtonClicked() {
            discardEvent();
        }
    }

    /**
     * The solver of the given row (Swing getSolver: matched by solver index).
     */
    private @Nullable IsabelleSolver getSolver(int row) {
        return row >= 0 && row < solvers.size() ? solvers.get(row) : null;
    }

    // --- verify harness seams (key.fx.verify.isabelle, see IsabelleVerifyF) ---------------------

    /** The current progress dialog, may be {@code null} before {@link #launcherStarted}. */
    IsabelleSolverProgressDialogF dialog() {
        return dialog;
    }

    /** The last overall progress text set by {@link #setProgressText(int)}. */
    String overallText() {
        return overallText;
    }

    /** Shows the information window of the solver at the given row. */
    void info(int row) {
        IsabelleSolver solver = getSolver(row);
        if (solver != null) {
            showInformation(solver);
        }
    }
}
