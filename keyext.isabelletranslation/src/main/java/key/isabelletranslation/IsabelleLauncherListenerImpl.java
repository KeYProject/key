package key.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import key.isabelletranslation.gui.IsabelleProgressDialog;
import key.isabelletranslation.gui.IsabelleProgressModel;

import javax.swing.*;
import java.awt.*;
import java.util.Timer;
import java.util.Collection;
import java.util.TimerTask;

public class IsabelleLauncherListenerImpl implements IsabelleLauncherListener {
    private final Timer timer = new Timer();
    private int finishedCounter = 0;


    private final static ColorSettings.ColorProperty RED =
            ColorSettings.define("[solverListener]red", "", new Color(180, 43, 43));

    private final static ColorSettings.ColorProperty GREEN =
            ColorSettings.define("[solverListener]green", "", new Color(43, 180, 43));

    @Override
    public void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolver> finishedInstances) {

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
            // switch to new open goal
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
        if (bar.getMaximum() == 1) {
            if (value == -1) {
                bar.setString("Preparing...");
                bar.setStringPainted(true);
                return;
            }
            bar.setString(value == 0 ? "Processing..." : "Finished.");
            bar.setStringPainted(true);
        } else {
            bar.setString("Processed " + value + " of " + bar.getMaximum() + " problems.");
            bar.setStringPainted(true);
        }
    }

    protected void discardEvent(IsabelleLauncher launcher) {

    }

    public IsabelleLauncherListenerImpl(IsabelleTranslationSettings settings) {

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
        progressModel.setText("Waiting...", 0, solver.getSolverIndex());
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