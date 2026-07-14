/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.gui.controller;

import java.awt.*;
import java.text.DecimalFormat;
import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.Timer;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.isabelletranslation.automation.IsabelleLauncher;
import org.key_project.isabelletranslation.automation.IsabelleLauncherListener;
import org.key_project.isabelletranslation.automation.IsabelleResult;
import org.key_project.isabelletranslation.automation.IsabelleSolver;
import org.key_project.isabelletranslation.gui.InformationWindow;
import org.key_project.isabelletranslation.gui.IsabelleProgressDialog;
import org.key_project.isabelletranslation.gui.IsabelleProgressModel;
import org.key_project.isabelletranslation.gui.IsabelleProofApplyUserAction;

/**
 * Updates the {@link IsabelleProgressDialog} for a given {@link IsabelleLauncher}.
 */
public class IsabelleLauncherProgressDialogMediator implements IsabelleLauncherListener {
    /**
     * The format used to display the remaining time for solver instances.
     */
    private static final DecimalFormat remainingTimeFormat = new DecimalFormat("#.#");

    /**
     * The Resolution used for the progress bars in the Isabelle dialog.
     */
    private static final int RESOLUTION = 1000;

    /**
     * The red color used to display the exception status for solvers
     */
    private final static ColorSettings.ColorProperty RED =
        ColorSettings.define("[isabelleDialog]red", "", new Color(180, 43, 43));

    /**
     * The green color used to display the valid status for solvers
     */
    private final static ColorSettings.ColorProperty GREEN =
        ColorSettings.define("[isabelleDialog]green", "", new Color(43, 180, 43));

    /**
     * Timer used to schedule periodic refreshes of the Isabelle dialog.
     */
    private final Timer timer = new Timer();

    /**
     * The proof which the launcher is working on.
     * Used to close solved goals.
     */
    private final Proof proof;

    /**
     * Indicates whether a user initiated stop has occured
     */
    private boolean userStopFlag = false;

    /**
     * The launcher used in conjunction with the dialog.
     */
    private final IsabelleLauncher launcher;

    /**
     * The number of finished instances.
     */
    private int finishedCounter = 0;

    /**
     * The solvers started by the launcher
     */
    private Collection<IsabelleSolver> solvers;

    /**
     * The {@link IsabelleProgressModel} associated with the launcher
     */
    private IsabelleProgressModel progressModel;

    /**
     * Stores which solvers have processed their problem
     */
    private boolean[][] finishedSolvers;

    /**
     * The dialog used
     */
    private IsabelleProgressDialog progressDialog;

    @Override
    public void launcherStopped(IsabelleLauncher launcher,
            Collection<IsabelleSolver> finishedInstances) {
        timer.cancel();

        setProgressText(finishedInstances.size());
        progressModel.setEditable(true);
        refreshDialog();
        progressDialog.setModus(IsabelleProgressDialog.Modus.SOLVERS_DONE);
    }

    @Override
    public void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers) {
        prepareDialog(solvers);

        setProgressText(-1);
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
        setProgressText(0);
    }

    /**
     * The event that occurs after the stop button has been pressed in the dialog.
     * Uses {@link IsabelleLauncher#stopAll()} to interrupt the
     * launcher.
     * Also sets the userStopFlag so solver interrupts can be allocated to the user.
     */
    protected void stopEvent() {
        userStopFlag = true;
        launcher.stopAll();
    }

    /**
     * The event that occurs after the apply button has been pressed in the dialog.
     * Invokes the {@link IsabelleLauncherProgressDialogMediator#applyResults()} to close solved
     * goals.
     * Then disposes of the dialog.
     */
    protected void applyEvent() {
        applyResults();
        progressDialog.dispose();
    }

    /**
     * Creates a action, which can close the solved goals.
     */
    private void applyResults() {
        KeYMediator mediator = MainWindow.getInstance().getMediator();
        // ensure that the goal closing does not lag the UI
        mediator.stopInterface(true);
        try {
            new IsabelleProofApplyUserAction(mediator, proof, solvers).actionPerformed(null);
        } finally {
            mediator.startInterface(true);
            // switch to new open goal
            mediator.getSelectionModel().defaultSelection();
        }
    }

    /**
     * Updates the dialog for a stopped solver depending on its result.
     *
     * @param solver The stopped solver.
     */
    private void stopped(IsabelleSolver solver) {
        int x = 0;
        int y = solver.getSolverIndex();

        if (!finishedSolvers[x][y]) {
            finishedCounter++;
            progressDialog.setProgress(finishedCounter);
            JProgressBar bar = progressDialog.getProgressBar();
            bar.setValue(finishedCounter);
            setProgressText(finishedCounter);
            finishedSolvers[x][y] = true;
        }

        IsabelleResult result = solver.getFinalResult();

        switch (result.getType()) {
            case INTERRUPTED:
                interrupted(x, y);
                break;
            case SUCCESS:
                successfullyStopped(solver, x, y);
                break;
            case ERROR:
                encounteredError(x, y);
                break;
            case TIMEOUT:
                timedOut(x, y);
                break;
            default:
                unknownStopped(x, y);
                break;
        }
    }

    /**
     * Updates the dialog for an interrupted solver.
     *
     * @param x The solver type index
     * @param y The solver index as reported by {@link IsabelleSolver#getSolverIndex()}
     */
    private void interrupted(int x, int y) {
        if (userStopFlag) {
            progressModel.setProgress(0, x, y);
            progressModel.setText("Interrupted by user.", x, y);
        } else {
            throw new RuntimeException("Solver was interrupted for unknown reasons!");
        }
    }

    /**
     * Updates the dialog for solver that stopped successfully.
     *
     * @param x The solver type index
     * @param y The solver index as reported by {@link IsabelleSolver#getSolverIndex()}
     */
    private void successfullyStopped(IsabelleSolver solver, int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(GREEN.get(), x, y);

        String timeInfo = solver.getComputationTime().toMillis() / 1000d + "s";

        progressModel.setText("Valid (" + timeInfo + ")", x, y);
    }

    /**
     * Updates the dialog for solver that encountered an error.
     *
     * @param x The solver type index
     * @param y The solver index as reported by {@link IsabelleSolver#getSolverIndex()}
     */
    private void encounteredError(int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(RED.get(), x, y);
        progressModel.setText("Exception!", x, y);
    }

    /**
     * Updates the dialog for solver that timed out.
     *
     * @param x The solver type index
     * @param y The solver index as reported by {@link IsabelleSolver#getSolverIndex()}
     */
    private void timedOut(int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setText("Timeout.", x, y);
    }

    /**
     * Updates the dialog for solver that stopped for unknown reasons.
     *
     * @param x The solver type index
     * @param y The solver index as reported by {@link IsabelleSolver#getSolverIndex()}
     */
    private void unknownStopped(int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(Color.BLUE, x, y);
        progressModel.setText("Unknown.", x, y);
    }

    /**
     * Sets the progress text based on the number of solver instances that have processed their
     * problem.
     * A negative value may be used to indicate the Launcher is still preparing.
     *
     * @param value The number of solvers that have processed their problem. Negative values
     *        indicate the launcher is still preparing.
     */
    private void setProgressText(int value) {
        JProgressBar bar = progressDialog.getProgressBar();
        if (value < 0) {
            bar.setString("Preparing... (this might take a few seconds)");
            bar.setStringPainted(true);
        } else {
            bar.setString("Processed " + value + " of " + bar.getMaximum() + " problems.");
            bar.setStringPainted(true);
        }
    }

    /**
     * The event that occurs after the discard button was pressed.
     * Disposes of the dialog and does nothing else, as the button is only available once the
     * launcher has stopped.
     */
    protected void discardEvent() {
        progressDialog.dispose();
    }

    /**
     * Creates a new mediator for the given proof and launcher
     *
     * @param proof the given proof
     * @param launcher the launcher used
     */
    public IsabelleLauncherProgressDialogMediator(Proof proof, IsabelleLauncher launcher) {
        this.proof = proof;
        this.launcher = launcher;
    }

    /**
     * Prepares the dialog. Opens the dialog.
     * Assigns the titles of all solver types to their columns.
     * Assigns the titles of all goals to be processed by the launcher.
     *
     * @param solvers The solvers to be started by the launcher.
     */
    private void prepareDialog(Collection<IsabelleSolver> solvers) {
        this.solvers = solvers;
        progressModel = new IsabelleProgressModel();

        String[] captions = new String[solvers.size()];

        int i = 0;
        for (IsabelleSolver solver : solvers) {
            captions[i] = solver.getProblem().getName();
            i++;
        }

        progressModel.addColumn(new IsabelleProgressModel.TitleColumn(captions));
        finishedSolvers = new boolean[1][solvers.size()];
        progressModel.addColumn(new IsabelleProgressModel.ProcessColumn(solvers.size()));


        progressDialog = new IsabelleProgressDialog(progressModel,
            new IsabelleProgressDialogListenerImpl(), false,
            RESOLUTION, solvers.size(), "", "Isabelle");


        SwingUtilities.invokeLater(() -> progressDialog.setVisible(true));
    }

    /**
     * Refreshes the progress of all solvers.
     */
    private void refreshDialog() {
        for (IsabelleSolver solver : solvers) {
            refreshProgressOfSolver(solver);
        }
    }

    /**
     * Refreshes the progress of a given solver by calling the requisite method in this class.
     *
     * @param solver the given solver
     */
    private void refreshProgressOfSolver(IsabelleSolver solver) {
        IsabelleSolver.SolverState state = solver.getState();
        switch (state) {
            case Preparing -> preparing(solver);
            case Parsing -> parsing(solver);
            case Running -> running(solver);
            case Stopped -> stopped(solver);
            case Waiting -> waiting(solver);
        }
    }

    /**
     * Updates the dialog for a running solver.
     * Updates the progress bar for this solver.
     *
     * @param solver the running solver
     */
    private void running(IsabelleSolver solver) {
        long progress = calculateProgress(solver);
        progressModel.setProgress((int) progress, 0, solver.getSolverIndex());

        float remainingTime = calculateRemainingTime(solver);
        progressModel.setText(remainingTimeFormat.format(remainingTime) + " sec.", 0,
            solver.getSolverIndex());
    }

    /**
     * Calculates the amount of progress made as a product of the percentage of the time passed in
     * comparison to the timeout duration of the solver and the RESOLUTION of the progress bar.
     *
     * @param solver The solver whose progress is calculated
     * @return The value which reflects the progress made by the solver
     */
    private long calculateProgress(IsabelleSolver solver) {
        Duration maxDuration = Duration.ofSeconds(solver.getTimeout());
        Instant startTime = solver.getStartTime();

        return (long) Math.floor(RESOLUTION
                * (Duration.between(startTime, Instant.now()).toMillis()
                        / (double) maxDuration.toMillis()));
    }

    /**
     * Calculates the time remaining until the timeout of the solver.
     *
     * @param solver the given solver whose remaining time will be calculated
     * @return The remaining time in seconds
     */
    private float calculateRemainingTime(IsabelleSolver solver) {
        Instant timeoutTime = solver.getStartTime().plusSeconds(solver.getTimeout());
        return Duration.between(Instant.now(), timeoutTime).toMillis() / 1000f;
    }

    /**
     * Updates the progress bar of a solver which is currently parsing the Isabelle theory for its
     * problem.
     *
     * @param solver the solver whose progress bar will be updated
     */
    private void parsing(IsabelleSolver solver) {
        progressModel.setText("Parsing...", 0, solver.getSolverIndex());
    }

    /**
     * Updates the progress bar of a solver that is waiting to be started.
     *
     * @param solver the solver whose progress bar will be updated
     */
    private void waiting(IsabelleSolver solver) {
    }

    private IsabelleSolver getSolver(int column, int row) {
        // This needs to be changed, if different kinds of Isabelle solvers are supported
        return solvers.stream().filter(s -> (s.getSolverIndex() == row)).findFirst().orElse(null);
    }

    /**
     * Updates the progress bar of a solver that is currently preparing.
     *
     * @param solver the solver whose progress bar will be updated
     */
    private void preparing(IsabelleSolver solver) {
        progressModel.setText("Preparing...", 0, solver.getSolverIndex());
    }

    /**
     * Naive implementation of a dialog listener to react to button inputs by the user.
     */
    private class IsabelleProgressDialogListenerImpl
            implements IsabelleProgressDialog.IsabelleProgressDialogListener {


        public IsabelleProgressDialogListenerImpl() {
            super();
        }

        @Override
        public void infoButtonClicked(int column, int row) {
            IsabelleSolver solver = getSolver(column, row);
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

    private void showInformation(IsabelleSolver solver) {
        Collection<InformationWindow.Information> information = new HashSet<>();
        String informationTitle = solver.name() + ": " + solver.getProblem().getName();

        information.add(new InformationWindow.Information("Translation theory",
            solver.getRawSolverInput(), informationTitle));
        if (solver.getFinalResult().isError()) {
            information.add(new InformationWindow.Information("Exception",
                solver.getFinalResult().getException().getMessage(), informationTitle));
        } else {
            information.add(new InformationWindow.Information("Raw Solver Output",
                solver.getRawSolverOutput(), informationTitle));
        }

        new InformationWindow(progressDialog, information,
            "Information for " + informationTitle);
    }
}
