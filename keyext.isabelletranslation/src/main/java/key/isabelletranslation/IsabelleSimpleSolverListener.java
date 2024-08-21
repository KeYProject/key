package key.isabelletranslation;

import de.uka.ilkd.key.gui.smt.ProgressDialog;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.smt.SolverLauncher;
import key.isabelletranslation.gui.IsabelleProgressDialog;
import key.isabelletranslation.gui.IsabelleProgressModel;

import javax.swing.*;
import java.util.Collection;

public class IsabelleSimpleSolverListener implements IsabelleLauncherListener {
    @Override
    public void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolverInstance> finishedInstances) {

    }

    @Override
    public void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleProblem> problems) {
        prepareDialog(problems, launcher);
    }

    protected void stopEvent(IsabelleLauncher launcher) {

    }

    protected void applyEvent(IsabelleLauncher launcher) {

    }

    protected void discardEvent(IsabelleLauncher launcher) {

    }

    public IsabelleSimpleSolverListener(IsabelleTranslationSettings settings) {

    }


    private static final int RESOLUTION = 1000;

    private Collection<IsabelleProblem> problems;
    private IsabelleProgressModel progressModel;
    private boolean[] problemProcessed;
    private IsabelleProgressDialog progressDialog;

    private void prepareDialog(Collection<IsabelleProblem> problems, final IsabelleLauncher launcher) {
        this.problems = problems;
        progressModel = new IsabelleProgressModel();

        String[] captions = new String[problems.size()];

        int i = 0;
        for (IsabelleProblem problem : problems) {
            captions[i] = "Problem " + i;
            i++;
        }

        progressModel.addColumn(new IsabelleProgressModel.TitleColumn(captions));
        problemProcessed = new boolean[problems.size()];
        progressModel.addColumn(new IsabelleProgressModel.ProcessColumn(problems.size()));

        for (IsabelleProblem problem : problems) {

        }


        progressDialog = new IsabelleProgressDialog(progressModel, new IsabelleProgressDialogListenerImpl(launcher), false,
                RESOLUTION, problems.size(), new String[] {}, (new String[]{"Isabelle"}));


        SwingUtilities.invokeLater(() -> progressDialog.setVisible(true));

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
