package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Calendar;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Timer;
import java.util.TimerTask;

import javax.swing.JOptionPane;
import javax.swing.JProgressBar;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.smt.InformationWindow.Information;
import de.uka.ilkd.key.gui.smt.ProgressDialog.Modus;
import de.uka.ilkd.key.gui.smt.ProgressDialog.ProgressDialogListener;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

public class SolverListener implements SolverLauncherListener {
    private ProgressDialog progressDialog;
    private ProgressModel progressModel;
    // Every intern SMT problem refers to one solver
    private Collection<InternSMTProblem> problems = new LinkedList<InternSMTProblem>();
    // Every SMT problem refers to many solvers.
    private Collection<SMTProblem> smtProblems = new LinkedList<SMTProblem>();
    private boolean[][] problemProcessed;
    private int finishedCounter;
    private Timer timer = new Timer();
    private final DefaultSMTSettings settings;
    private final Proof smtProof;
    private final static ColorSettings.ColorProperty RED =
        ColorSettings.define("[solverListener]red", "", new Color(180, 43, 43));

    private final static ColorSettings.ColorProperty GREEN =
        ColorSettings.define("[solverListener]green", "", new Color(43, 180, 43));

    private static int FILE_ID = 0;

    private static final int RESOLUTION = 1000;

    public static class InternSMTProblem {
        final int problemIndex;
        final int solverIndex;
        final SMTSolver solver;
        final SMTProblem problem;
        final LinkedList<Information> information = new LinkedList<Information>();
        private boolean stopped = false;
        private boolean running = false;

        private long timeToSolve;

        public InternSMTProblem(int problemIndex, int solverIndex, SMTProblem problem,
                SMTSolver solver) {
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

        private void addInformation(String title, String content) {
            information.add(new Information(title, content, solver.name()));
        }

        public void createInformation() {
            if (solver.getException() != null) {

                StringWriter writer = new StringWriter();

                solver.getException().printStackTrace(new PrintWriter(writer));
                addInformation("Error-Message",
                    solver.getException().toString() + "\n\n" + writer.toString());


            }
            addInformation("Solver Input", solver.getRawSolverInput());
            if (solver.getTacletTranslation() != null) {
                addInformation("Taclets", solver.getTacletTranslation().toString());
            }
            addInformation("Solver Output", solver.getRawSolverOutput());

            Collection<Throwable> exceptionsOfTacletTranslation =
                solver.getExceptionsOfTacletTranslation();
            if (!exceptionsOfTacletTranslation.isEmpty()) {
                String exceptionText =
                    "The following exceptions have ocurred while translating the taclets:\n\n";
                int i = 1;
                for (Throwable e : exceptionsOfTacletTranslation) {
                    exceptionText += i + ". " + e.getMessage();
                    StringWriter sw = new StringWriter();
                    PrintWriter pw = new PrintWriter(sw);
                    e.printStackTrace(pw);
                    exceptionText += "\n\n" + sw.toString();
                    exceptionText += "\n #######################\n\n";
                    i++;
                }
                addInformation("Warning", exceptionText);
            }

            if (solver.getType().supportHasBeenChecked()
                    && !solver.getType().isSupportedVersion()) {
                addInformation("Solver Support", computeSolverTypeWarningMessage(solver.getType()));
            }

            solver.getException();
        }

        public LinkedList<Information> getInformation() {
            return information;
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


    public SolverListener(DefaultSMTSettings settings, Proof smtProof) {
        this.settings = settings;
        this.smtProof = smtProof;
    }

    @Override
    public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> problemSolvers) {
        timer.cancel();


        storeInformation();
        progressModel.setEditable(true);
        refreshDialog();
        progressDialog.setModus(Modus.discardModus);
        for (InternSMTProblem problem : problems) {
            problem.createInformation();
        }
        if (settings.getModeOfProgressDialog() == ProofIndependentSMTSettings.ProgressMode.CLOSE) {
            applyEvent(launcher);
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
        KeYMediator mediator = MainWindow.getInstance().getMediator();
        mediator.stopInterface(true);
        try {
            for (SMTProblem problem : smtProblems) {
                if (problem.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                    IBuiltInRuleApp app =
                        RuleAppSMT.rule.createApp(null).setTitle(getTitle(problem));
                    problem.getGoal().apply(app);
                }
            }
        } finally {
            mediator.startInterface(true);
        }

    }

    private void showInformation(InternSMTProblem problem) {
        new InformationWindow(progressDialog, problem.solver, problem.information,
            "Information for " + problem.toString());
    }

    private void prepareDialog(Collection<SMTProblem> smtproblems,
            Collection<SolverType> solverTypes, final SolverLauncher launcher) {
        this.smtProblems = smtproblems;
        progressModel = new ProgressModel();

        String[] captions = new String[smtProblems.size()];

        int i = 0;
        for (SMTProblem problem : smtproblems) {
            captions[i] = problem.getName();
            i++;
        }

        progressModel.addColumn(new ProgressModel.TitleColumn(captions));
        String[] titles = new String[solverTypes.size() + 1];
        problemProcessed = new boolean[solverTypes.size()][smtProblems.size()];
        titles[0] = "";
        i = 1;
        for (SolverType type : solverTypes) {
            progressModel.addColumn(new ProgressModel.ProcessColumn(smtproblems.size()));
            titles[i] = type.getName();
            i++;
        }

        int x = 0, y = 0;
        for (SMTProblem problem : smtproblems) {
            y = 0;
            for (SMTSolver solver : problem.getSolvers()) {
                this.problems.add(new InternSMTProblem(x, y, problem, solver));
                y++;
            }
            x++;
        }



        boolean ce = solverTypes.contains(SolverTypes.Z3_CE_SOLVER);



        progressDialog =
            new ProgressDialog(progressModel, new ProgressDialogListenerImpl(launcher, ce), ce,
                RESOLUTION, smtproblems.size() * solverTypes.size(), new String[] {}, titles);

        SwingUtilities.invokeLater(new Runnable() {

            @Override
            public void run() {
                progressDialog.setVisible(true);
            }
        });

    }



    private InternSMTProblem getProblem(int col, int row) {
        for (InternSMTProblem problem : problems) {
            if (problem.problemIndex == row && problem.solverIndex == col) {
                return problem;
            }
        }
        // This case will be entered if the columns or rows of the ProgressDialog table are moved!
        return null;
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
            final Collection<SolverType> solverTypes, final SolverLauncher launcher) {
        prepareDialog(smtproblems, solverTypes, launcher);

        setProgressText(0);
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
        problem.startTime();
        long progress = calculateProgress(problem);
        progressModel.setProgress((int) progress, problem.getSolverIndex(),
            problem.getProblemIndex());
        float remainingTime = calculateRemainingTime(problem);
        progressModel.setText(Float.toString(remainingTime) + " sec.", problem.getSolverIndex(),
            problem.getProblemIndex());
    }

    private void setProgressText(int value) {
        JProgressBar bar = progressDialog.getProgressBar();
        if (bar.getMaximum() == 1) {
            bar.setString(value == 0 ? "Processing..." : "Finished.");
            bar.setStringPainted(true);
        } else {
            bar.setString("Processed " + value + " of " + bar.getMaximum() + " problems.");
            bar.setStringPainted(true);
        }

    }

    private void stopped(InternSMTProblem problem) {
        problem.stopTime();

        int x = problem.getSolverIndex();
        int y = problem.getProblemIndex();

        if (!problemProcessed[x][y]) {
            finishedCounter++;
            progressDialog.setProgress(finishedCounter);
            JProgressBar bar = progressDialog.getProgressBar();
            bar.setValue(finishedCounter);
            setProgressText(finishedCounter);
            problemProcessed[x][y] = true;
        }

        if (problem.solver.wasInterrupted()) {
            interrupted(problem);
        } else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.VALID) {

            successfullyStopped(problem, x, y);
        } else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE) {

            unsuccessfullyStopped(problem, x, y);
        } else {

            unknownStopped(x, y);
        }

    }

    private void interrupted(InternSMTProblem problem) {
        ReasonOfInterruption reason = problem.solver.getReasonOfInterruption();
        int x = problem.getSolverIndex();
        int y = problem.getProblemIndex();
        switch (reason) {
        case Exception:
            progressModel.setProgress(0, x, y);
            progressModel.setTextColor(RED.get(), x, y);
            progressModel.setText("Exception!", x, y);



            break;
        case NoInterruption:
            throw new RuntimeException("This position should not be reachable!");

        case Timeout:
            progressModel.setProgress(0, x, y);
            progressModel.setText("Timeout.", x, y);

            break;
        case User:
            progressModel.setText("Interrupted by user.", x, y);
            break;
        }
    }

    private void successfullyStopped(InternSMTProblem problem, int x, int y) {
        String timeInfo = " (" + problem.getTimeInSecAsString() + ")";

        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(GREEN.get(), x, y);
        if (problem.solver.getType() == SolverTypes.Z3_CE_SOLVER) {
            progressModel.setText("No Counterexample.", x, y);
        } else {
            progressModel.setText("Valid" + timeInfo, x, y);
        }


    }

    private void unsuccessfullyStopped(InternSMTProblem problem, int x, int y) {
        String timeInfo = " (" + problem.getTimeInSecAsString() + ")";
        if (problem.solver.getType() == SolverTypes.Z3_CE_SOLVER) {
            progressModel.setProgress(0, x, y);
            progressModel.setTextColor(RED.get(), x, y);
            progressModel.setText("Counter Example" + timeInfo, x, y);
        } else {
            progressModel.setProgress(0, x, y);
            Color c = new Color(200, 150, 0);
            progressModel.setTextColor(c, x, y);
            progressModel.setText("Possible Counter Example" + timeInfo, x, y);
        }
    }

    private void unknownStopped(int x, int y) {
        progressModel.setProgress(0, x, y);
        progressModel.setTextColor(Color.BLUE, x, y);
        progressModel.setText("Unknown.", x, y);
    }

    private void storeInformation() {

        if (settings.storeSMTTranslationToFile()
                || (settings.makesUseOfTaclets() && settings.storeTacletTranslationToFile())) {
            for (InternSMTProblem problem : problems) {
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

        String fileName = goal.proof().name() + "_" + goal.getTime() + "_" + solver.name() + ".smt";
        path = path + File.separator + fileName;
        path = finalizePath(path, solver, goal);
        storeToFile(problemString, path);

    }

    private void storeToFile(String text, String path) {
        try {
            final BufferedWriter out2 = new BufferedWriter(new FileWriter(path));
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


    public static String computeSolverTypeWarningMessage(SolverType type) {
        StringBuffer message = new StringBuffer();
        message.append("You are using a version of " + type.getName()
            + " which has not been tested for this version of KeY.\nIt can therefore be that"
            + " errors occur that would not occur\nusing the following version or higher:\n");
        message.append(type.getMinimumSupportedVersion());
        return message.toString();
    }

    private class ProgressDialogListenerImpl implements ProgressDialogListener {



        private SolverLauncher launcher;
        private boolean counterexample;



        public ProgressDialogListenerImpl(SolverLauncher launcher, boolean counterexample) {
            super();
            this.launcher = launcher;
            this.counterexample = counterexample;
        }

        @Override
        public void infoButtonClicked(int column, int row) {
            InternSMTProblem problem = getProblem(column, row);
            showInformation(problem);

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
            // remove semantics blasting proof for ce dialog
            if (counterexample && smtProof != null) {
                smtProof.dispose();
            }

        }

        @Override
        public void additionalInformationChosen(Object obj) {
            if (obj instanceof String) {
                JOptionPane.showOptionDialog(progressDialog, obj, "Warning",
                    JOptionPane.DEFAULT_OPTION, JOptionPane.WARNING_MESSAGE, null, null, null);
            } else if (obj instanceof InternSMTProblem) {
                showInformation((InternSMTProblem) obj);
            }
        }
    };

    /**
     * Checks if the given {@link Term} contains a modality, query, or update.
     *
     * @param term The {@link Term} to check.
     * @return {@code true} contains at least one modality or query, {@code false} contains no
     *         modalities and no queries.
     */
    public static boolean containsModalityOrQuery(Term term) {
        ContainsModalityOrQueryVisitor visitor = new ContainsModalityOrQueryVisitor();
        term.execPostOrder(visitor);
        return visitor.containsModOrQuery();
    }

    /**
     * Utility class used to check whether a term contains constructs that are not handled by the
     * SMT translation. Stolen from a very similar class by Martin Hentschel. Maybe should go to a
     * utility class.
     *
     * @author jschiffl
     */
    protected static class ContainsModalityOrQueryVisitor extends DefaultVisitor {
        /**
         * The result.
         */
        boolean containsModQuery = false;

        /**
         * {@inheritDoc}
         */
        @Override
        public void visit(Term visited) {
            if (visited.op() instanceof Modality || visited.op() instanceof IProgramMethod) {
                containsModQuery = true;
            }
        }

        /**
         * Returns the result.
         *
         * @return {@code true} contains at least one modality, query, or update; {@code false}
         *         contains no modalities, no queries, and no updates.
         */
        public boolean containsModOrQuery() {
            return containsModQuery;
        }
    }

}
