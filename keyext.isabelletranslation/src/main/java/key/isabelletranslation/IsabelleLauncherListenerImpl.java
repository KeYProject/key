package key.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import key.isabelletranslation.gui.IsabelleProgressDialog;
import key.isabelletranslation.gui.IsabelleProgressModel;

import javax.swing.*;
import java.util.Timer;
import java.util.Collection;
import java.util.TimerTask;

public class IsabelleLauncherListenerImpl implements IsabelleLauncherListener {
    private final Timer timer = new Timer();

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
    private boolean[] problemProcessed;
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
        problemProcessed = new boolean[solvers.size()];
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

    private void stopped(IsabelleSolver solver) {
        progressModel.setText("Stopped...", 0, solver.getSolverIndex());
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
