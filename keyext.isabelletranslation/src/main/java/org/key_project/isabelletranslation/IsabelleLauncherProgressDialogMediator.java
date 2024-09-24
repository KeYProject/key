package org.key_project.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.isabelletranslation.gui.IsabelleProgressDialog;
import org.key_project.isabelletranslation.gui.IsabelleProgressModel;
import org.key_project.isabelletranslation.gui.ProofApplyUserAction;

import javax.swing.*;
import java.awt.*;
import java.util.Timer;
import java.util.Collection;
import java.util.TimerTask;

public class IsabelleLauncherProgressDialogMediator implements IsabelleLauncherListener {
    private final Timer timer = new Timer();
    private int finishedCounter = 0;

    private final Proof proof;
    private final IsabelleTranslationSettings settings;


    private final static ColorSettings.ColorProperty RED =
            ColorSettings.define("[isabelleDialog]red", "", new Color(180, 43, 43));

    private final static ColorSettings.ColorProperty GREEN =
            ColorSettings.define("[isabelleDialog]green", "", new Color(43, 180, 43));

    @Override
    public void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolver> finishedInstances) {
        timer.cancel();

        progressModel.setEditable(true);
        refreshDialog();
        progressDialog.setModus(IsabelleProgressDialog.Modus.SOLVERS_DONE);

        //TODO automatic closing of goals without apply button?
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
            //TODO create own close action
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

        if (solver.wasInterrupted()) {
            interrupted(solver);
        } else if (solver.getFinalResult().isSuccessful()) {
            successfullyStopped(solver, x, y);
        } else {
            unknownStopped(x, y);
        }
    }

    private void interrupted(IsabelleSolver solver) {
        IsabelleSolver.ReasonOfInterruption reason = solver.getReasonOfInterruption();
        int x = 0;
        int y = solver.getSolverIndex();
        switch (reason) {
            case Exception -> {
                progressModel.setProgress(0, x, y);
                progressModel.setTextColor(RED.get(), x, y);
                progressModel.setText("Exception!", x, y);
            }
            case NoInterruption -> throw new RuntimeException("This position should not be reachable!");
            case Timeout -> {
                progressModel.setProgress(0, x, y);
                progressModel.setText("Timeout.", x, y);
            }
            case User -> progressModel.setText("Interrupted by user.", x, y);
        }
    }

    private void successfullyStopped(IsabelleSolver solver, int x, int y) {
        //TODO add time information

        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(GREEN.get(), x, y);
        progressModel.setText("Valid", x, y);
    }

    private void unknownStopped(int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(Color.BLUE, x, y);
        progressModel.setText("Unknown.", x, y);
    }

    private void setProgressText(int value) {
        JProgressBar bar = progressDialog.getProgressBar();
            if (value == -1) {
                bar.setString("Preparing...");
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

    public IsabelleLauncherProgressDialogMediator(IsabelleTranslationSettings settings, Proof proof) {
        this.settings = settings;
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

    private boolean refreshProgressOfSolver(IsabelleSolver solver) {
        IsabelleSolver.SolverState state = solver.getState();
        return switch (state) {
            case Preparing -> {
                preparing(solver);
                yield true;
            }
            case Parsing -> {
                parsing(solver);
                yield true;
            }
            case Running -> {
                running(solver);
                yield true;
            }
            case Stopped -> {
                stopped(solver);
                yield false;
            }
            case Waiting -> {
                waiting(solver);
                yield true;
            }
        };

    }

    private void running(IsabelleSolver solver) {
        progressModel.setText("Running...", 0, solver.getSolverIndex());
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
            //SolverListener.InternSMTProblem problem = getProblem(column, row);
            //showInformation(problem);
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
