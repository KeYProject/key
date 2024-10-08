package org.key_project.isabelletranslation.automation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.isabelletranslation.gui.IsabelleProgressDialog;
import org.key_project.isabelletranslation.gui.IsabelleProgressModel;
import org.key_project.isabelletranslation.gui.ProofApplyUserAction;

import javax.swing.*;
import java.awt.*;
import java.text.DecimalFormat;
import java.time.Duration;
import java.time.Instant;
import java.util.Timer;
import java.util.Collection;
import java.util.TimerTask;

public class IsabelleLauncherProgressDialogMediator implements IsabelleLauncherListener {
    private static final DecimalFormat remainingTimeFormat = new DecimalFormat("#.#");
    private final Timer timer = new Timer();
    private int finishedCounter = 0;

    private final Proof proof;


    private final static ColorSettings.ColorProperty RED =
            ColorSettings.define("[isabelleDialog]red", "", new Color(180, 43, 43));

    private final static ColorSettings.ColorProperty GREEN =
            ColorSettings.define("[isabelleDialog]green", "", new Color(43, 180, 43));
    private boolean userStopFlag = false;

    @Override
    public void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolver> finishedInstances) {
        timer.cancel();

        progressModel.setEditable(true);
        refreshDialog();
        progressDialog.setModus(IsabelleProgressDialog.Modus.SOLVERS_DONE);
    }

    @Override
    public void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers) {
        prepareDialog(solvers, launcher);

        setProgressText(-1);
        timer.schedule(new TimerTask() {
            @Override
            public void run() {
                refreshDialog();
            }
        }, 0, 10);
    }

    @Override
    public void launcherPreparationFinished(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers) {
        setProgressText(0);
    }

    protected void stopEvent(IsabelleLauncher launcher) {
        userStopFlag = true;
        launcher.stopAll(IsabelleSolver.ReasonOfInterruption.User);
    }

    protected void applyEvent(IsabelleLauncher launcher) {
        launcher.stopAll(IsabelleSolver.ReasonOfInterruption.NoInterruption);
        applyResults();
        progressDialog.dispose();
    }

    private void applyResults() {
        KeYMediator mediator = MainWindow.getInstance().getMediator();
        // ensure that the goal closing does not lag the UI
        mediator.stopInterface(true);
        try {
            new ProofApplyUserAction(mediator, proof, solvers).actionPerformed(null);
        } finally {
            mediator.startInterface(true);
            //switch to new open goal
            mediator.getSelectionModel().defaultSelection();
        }
    }

    private void stopped(IsabelleSolver solver) {
        int x = 0;
        int y = solver.getSolverIndex();

        if (!problemProcessed[x][y]) {
            finishedCounter++;
            progressDialog.setProgress(finishedCounter);
            JProgressBar bar = progressDialog.getProgressBar();
            bar.setValue(finishedCounter);
            setProgressText(finishedCounter);
            problemProcessed[x][y] = true;
        }

        IsabelleResult result = solver.getFinalResult();

        switch (result.getType()) {
            case INTERRUPTED:
                interrupted(solver, x, y);
                break;
            case SUCCESS:
                successfullyStopped(solver, x, y);
                break;
            case ERROR:
                encounteredError(solver, x, y);
                break;
            case TIMEOUT:
                timedOut(solver, x, y);
                break;
            default:
                unknownStopped(x, y);
                break;
        }
    }

    private void interrupted(IsabelleSolver solver, int x, int y) {
        if (userStopFlag) {
            progressModel.setProgress(0, x, y);
            progressModel.setText("Interrupted by user.", x, y);
        } else {
            throw new RuntimeException("This position should not be reachable!");
        }
    }

    private void successfullyStopped(IsabelleSolver solver, int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(GREEN.get(), x, y);

        String timeInfo = solver.getComputationTime().toMillis() / 1000d + "s";

        progressModel.setText("Valid (" + timeInfo + ")", x, y);
    }

    private void encounteredError(IsabelleSolver solver, int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(RED.get(), x, y);
        progressModel.setText("Exception!", x, y);
    }

    private void timedOut(IsabelleSolver solver, int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setText("Interrupted by User.", x, y);
    }

    private void unknownStopped(int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(Color.BLUE, x, y);
        progressModel.setText("Unknown.", x, y);
    }

    private void setProgressText(int value) {
        JProgressBar bar = progressDialog.getProgressBar();
            if (value == -1) {
                bar.setString("Preparing... (this might take a few seconds)");
                bar.setStringPainted(true);
            } else if (value == bar.getMaximum()){
                bar.setString("Finished.");
                bar.setStringPainted(true);
            } else {
                bar.setString("Processed " + value + " of " + bar.getMaximum() + " problems.");
                bar.setStringPainted(true);
            }
    }

    protected void discardEvent(IsabelleLauncher launcher) {
        launcher.stopAll(IsabelleSolver.ReasonOfInterruption.User);
        progressDialog.dispose();
    }

    public IsabelleLauncherProgressDialogMediator(Proof proof) {
        this.proof = proof;
    }


    private static final int RESOLUTION = 1000;

    private Collection<IsabelleSolver> solvers;
    private IsabelleProgressModel progressModel;
    private boolean[][] problemProcessed;
    private IsabelleProgressDialog progressDialog;

    private void prepareDialog(Collection<IsabelleSolver> solvers, final IsabelleLauncher launcher) {
        this.solvers = solvers;
        progressModel = new IsabelleProgressModel();

        String[] captions = new String[solvers.size()];

        int i = 0;
        for (IsabelleSolver solver : solvers) {
            captions[i] = solver.getProblem().getName();
            i++;
        }

        progressModel.addColumn(new IsabelleProgressModel.TitleColumn(captions));
        problemProcessed = new boolean[1][solvers.size()];
        progressModel.addColumn(new IsabelleProgressModel.ProcessColumn(solvers.size()));


        progressDialog = new IsabelleProgressDialog(progressModel, new IsabelleProgressDialogListenerImpl(launcher), false,
                RESOLUTION, solvers.size(), new String[] {}, "", "Isabelle");


        SwingUtilities.invokeLater(() -> progressDialog.setVisible(true));
    }

    private void refreshDialog() {
        for (IsabelleSolver solver : solvers) {
            refreshProgressOfSolver(solver);
        }
    }

    private void refreshProgressOfSolver(IsabelleSolver solver) {
        IsabelleSolver.SolverState state = solver.getState();
        switch (state) {
            case Preparing -> {
                preparing(solver);
            }
            case Parsing -> {
                parsing(solver);
            }
            case Running -> {
                running(solver);
            }
            case Stopped -> {
                stopped(solver);
            }
            case Waiting -> {
                waiting(solver);
            }
        }

    }

    private void running(IsabelleSolver solver) {
        long progress = calculateProgress(solver);
        progressModel.setProgress((int) progress, 0, solver.getSolverIndex());

        float remainingTime = calculateRemainingTime(solver);
        progressModel.setText(remainingTimeFormat.format(remainingTime) + " sec.", 0, solver.getSolverIndex());
    }

    private long calculateProgress(IsabelleSolver solver) {
        Duration maxDuration = Duration.ofSeconds(solver.getTimeout());
        Instant startTime = solver.getStartTime();

        return RESOLUTION * (Duration.between(startTime, Instant.now()).toMillis() / maxDuration.toMillis());
    }

    private float calculateRemainingTime(IsabelleSolver solver) {
        Instant timeoutTime = solver.getStartTime().plusSeconds(solver.getTimeout());
        return Duration.between(Instant.now(), timeoutTime).toMillis() / 1000f;
    }

    private void parsing(IsabelleSolver solver) {
        progressModel.setText("Parsing...", 0, solver.getSolverIndex());
    }

    private void waiting(IsabelleSolver solver) {
    }

    private void preparing(IsabelleSolver solver) {
        progressModel.setText("Preparing...", 0, solver.getSolverIndex());
    }

    private class IsabelleProgressDialogListenerImpl implements IsabelleProgressDialog.IsabelleProgressDialogListener {


        private final IsabelleLauncher launcher;


        public IsabelleProgressDialogListenerImpl(IsabelleLauncher launcher) {
            super();
            this.launcher = launcher;
        }

        @Override
        public void infoButtonClicked(int column, int row) {
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
            discardEvent(launcher);
        }
    }
}
