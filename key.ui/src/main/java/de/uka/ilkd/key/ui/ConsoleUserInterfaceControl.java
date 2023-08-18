/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ui;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.List;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Implementation of {@link UserInterfaceControl} used by command line interface of KeY.
 */
public class ConsoleUserInterfaceControl extends AbstractMediatorUserInterfaceControl {
    private static final Logger LOGGER = LoggerFactory.getLogger(ConsoleUserInterfaceControl.class);

    private static final int PROGRESS_BAR_STEPS = 50;
    private static final String PROGRESS_MARK = ">";

    // Substitute for TaskTree (GUI) to facilitate side proofs in console mode
    ImmutableList<Proof> proofStack = ImmutableSLList.nil();

    final KeYMediator mediator;

    // for a progress bar
    int progressMax = 0;


    // flag to indicate that a file should merely be loaded not proved. (for
    // "reload" testing)
    private final boolean loadOnly;


    /**
     * Current key problem file that is attempted to be proven.
     */
    private File keyProblemFile = null;

    /**
     * We want to record whether there was a proof that could not be proven. {@link Main} calls
     * System.exit() after all files have been loaded with {@link #loadProblem(java.io.File)}.
     * Program return value depends on whether there has been a proof attempt that was not
     * successful.
     */
    public boolean allProofsSuccessful = true;

    public ConsoleUserInterfaceControl(boolean loadOnly) {
        this.mediator = new KeYMediator(this);
        this.loadOnly = loadOnly;
    }

    private void printResults(final int openGoals, TaskFinishedInfo info, final Object result2) {
        LOGGER.info("]"); // end progress bar
        LOGGER.info("[ DONE  ... rule application ]");
        if (LOGGER.isDebugEnabled()) {
            LOGGER.debug("\n== Proof {} ==", (openGoals > 0 ? "open" : "closed"));
            final Statistics stat = info.getProof().getStatistics();
            LOGGER.debug("Proof steps: {}", stat.nodes);
            LOGGER.debug("Branches: {}", stat.branches);
            LOGGER.debug("Automode Time: {} ms", stat.autoModeTimeInMillis);
            LOGGER.debug("Time per step: {} ms", stat.timePerStepInMillis);
        }
        LOGGER.info("Number of goals remaining open: {}", openGoals);
        if (openGoals == 0) {
            LOGGER.info("Proved");
        } else {
            LOGGER.info("Not proved");
        }
        // this seems to be a good place to free some memory
        Runtime.getRuntime().gc();

        /*
         * It is assumed that this part of the code is never reached, unless a value has been
         * assigned to keyProblemFile in method loadProblem(File).
         */
        assert keyProblemFile != null : "Unexcpected null pointer. Trying to"
            + " save a proof but no corresponding key problem file is " + "available.";
        allProofsSuccessful &= saveProof(result2, info.getProof(), keyProblemFile);
        /*
         * We "delete" the value of keyProblemFile at this point by assigning null to it. That way
         * we prevent KeY from saving another proof (that belongs to another key problem file) for a
         * key problem file whose execution cycle has already been finished (and whose proof has
         * already been saved). It is assumed that a new value has been assigned beforehand in
         * method loadProblem(File), if this part of the code is reached again.
         */
        keyProblemFile = null;
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        super.taskFinished(info);
        progressMax = 0; // reset progress bar marker
        final Proof proof = info.getProof();
        if (proof == null) {
            final Object error = info.getResult();
            LOGGER.info("Proof loading failed");
            if (error instanceof Throwable) {
                LOGGER.info("Proof loading failed", (Throwable) error);
            } else {
                LOGGER.info("Proof loading failed");
            }
            System.exit(1);
        }
        final int openGoals = proof.openGoals().size();
        final Object result2 = info.getResult();
        if (info.getSource() instanceof ProverCore || info.getSource() instanceof ProofMacro) {
            if (!isAtLeastOneMacroRunning()) {
                printResults(openGoals, info, result2);
            }
        } else if (info.getSource() instanceof ProblemLoader) {
            LOGGER.debug("{}", result2);
            System.exit(-1);
        }
        if (loadOnly || openGoals == 0) {
            LOGGER.info("Number of open goals after loading: {}", openGoals);
            System.exit(0);
        }
        ProblemLoader problemLoader = (ProblemLoader) info.getSource();
        if (problemLoader.hasProofScript()) {
            try {
                Pair<String, Location> script = problemLoader.readProofScript();
                ProofScriptEngine pse = new ProofScriptEngine(script.first, script.second);
                this.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, "Script started", 0));
                pse.execute(this, proof);
                // The start and end messages are fake to persuade the system ...
                // All this here should refactored anyway ...
                this.taskFinished(new ProofMacroFinishedInfo(new SkipMacro(), proof));
            } catch (Exception e) {
                LOGGER.debug("", e);
                System.exit(-1);
            }
        } else if (macroChosen()) {
            applyMacro();
        } else {
            finish(proof);
        }
    }


    @Override
    public void taskStarted(TaskStartedInfo info) {
        super.taskStarted(info);
        progressMax = info.getSize();
        if (TaskKind.Strategy.equals(info.getKind())) {
            System.out.println(info.getMessage() + " ["); // start progress bar
        } else {
            System.out.println(info.getMessage());
        }
    }

    @Override
    public void loadProblem(File file) {
        /*
         * Current file is stored in a private field. It will be used in method printResults() to
         * determine file names, in which proofs will be written.
         */
        keyProblemFile = file;
        getProblemLoader(file, null, null, null, mediator).runSynchronously();
    }

    /**
     * loads the problem or proof from the given file
     *
     * @param file the File with the problem description or the proof
     * @param classPath the class path entries to use.
     * @param bootClassPath the boot class path to use.
     * @param includes the included files to use
     */
    public void loadProblem(File file, List<File> classPath, File bootClassPath,
            List<File> includes) {
        ProblemLoader problemLoader =
            getProblemLoader(file, classPath, bootClassPath, includes, getMediator());
        problemLoader.runAsynchronously();
    }

    @Override
    public void loadProofFromBundle(File proofBundle, File proofFilename) {
        ProblemLoader problemLoader =
            getProblemLoader(proofBundle, null, null, null, getMediator());
        problemLoader.setProofPath(proofFilename);
        problemLoader.runAsynchronously();
    }

    @Override
    public void registerProofAggregate(ProofAggregate pa) {
        super.registerProofAggregate(pa);
        mediator.setProof(pa.getFirstProof());
        proofStack = proofStack.prepend(pa.getFirstProof());
    }

    void finish(Proof proof) {
        // setInteractive(false) has to be called because the ruleAppIndex
        // has to be notified that we work in auto mode (CS)
        mediator.setInteractive(false);
        getProofControl().startAndWaitForAutoMode(proof);
        LOGGER.debug("{}", proof.getStatistics());
    }

    @Override
    public final void progressStarted(Object sender) {
        LOGGER.debug("ConsoleUserInterfaceControl.progressStarted({})", sender);
    }

    @Override
    public final void progressStopped(Object sender) {
        LOGGER.debug("ConsoleUserInterfaceControl.progressStopped({})", sender);
    }

    @Override
    public final void reportException(Object sender, ProofOblInput input, Exception e) {
        LOGGER.debug("ConsoleUserInterfaceControl.reportException({},{},{})", sender, input, e);
    }

    @Override
    public final void reportStatus(Object sender, String status, int progress) {
        LOGGER.debug("ConsoleUserInterfaceControl.reportStatus({},{},{})", sender, status,
            progress);
    }

    @Override
    public final void reportStatus(Object sender, String status) {
        LOGGER.debug("ConsoleUserInterfaceControl.reportStatus({},{})", sender, status);
    }

    @Override
    public final void resetStatus(Object sender) {
        LOGGER.debug("ConsoleUserInterfaceControl.resetStatus({})", sender);
    }

    @Override
    public final void taskProgress(int position) {
        super.taskProgress(position);
        if (progressMax > 0) {
            if ((position * PROGRESS_BAR_STEPS) % progressMax == 0) {
                System.out.print(PROGRESS_MARK);
            }
        }
    }

    @Override
    public final void setMaximum(int maximum) {
        LOGGER.debug("ConsoleUserInterfaceControl.setMaximum({})", maximum);
    }

    @Override
    public final void setProgress(int progress) {
        LOGGER.debug("ConsoleUserInterfaceControl.setProgress({})", progress);
    }

    @Override
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models, Goal goal) {
        LOGGER.debug("Taclet match completion not supported by console.");
    }

    @Override
    public final void openExamples() {
        LOGGER.info("Open Examples not suported by console UI.");
    }

    @Override
    public final ProblemInitializer createProblemInitializer(Profile profile) {
        return new ProblemInitializer(this, new Services(profile), this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        super.proofDisposing(e);
        if (!proofStack.isEmpty()) {
            Proof p = proofStack.head();
            proofStack = proofStack.removeAll(p);
            assert p.name().equals(e.getSource().name());
            mediator.setProof(proofStack.head());
        } else {
            // proofStack might be empty, though proof != null. This can
            // happen for symbolic execution tests, if proofCreated was not
            // called by the test setup.
        }
    }

    @Override
    public final boolean selectProofObligation(InitConfig initConfig) {
        ProofObligationSelector sel = new ConsoleProofObligationSelector(this, initConfig);
        return sel.selectProofObligation();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYMediator getMediator() {
        return mediator;
    }

    @Override
    public void notify(NotificationEvent event) {
        LOGGER.trace("{}", event);
    }

    @Override
    public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        return AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, forced);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void reportWarnings(ImmutableSet<PositionedString> warnings) {
        warnings.forEach(it -> LOGGER.info("{}", it));
    }

    /**
     * Save proof.
     *
     * @param result the result
     * @param proof the proof
     * @param keyProblemFile the key problem file
     * @return true, if successful
     */
    public static boolean saveProof(Object result, Proof proof, File keyProblemFile) {
        if (result instanceof Throwable) {
            throw new RuntimeException("Error in batchmode.", (Throwable) result);
        }

        // Save the proof before exit.
        String baseName = keyProblemFile.getAbsolutePath();
        int idx = baseName.indexOf(".key");
        if (idx == -1) {
            idx = baseName.indexOf(".proof");
        }
        baseName = baseName.substring(0, idx == -1 ? baseName.length() : idx);

        File f;
        int counter = 0;
        do {
            f = new File(baseName + ".auto." + counter + ".proof");
            counter++;
        } while (f.exists());

        try {
            // a copy with running number to compare different runs
            proof.saveToFile(new File(f.getAbsolutePath()));
            // save current proof under common name as well
            proof.saveToFile(new File(baseName + ".auto.proof"));

            // save proof statistics
            ShowProofStatistics.getCSVStatisticsMessage(proof);
            File file = new File(MiscTools.toValidFileName(proof.name().toString()) + ".csv");
            try (BufferedWriter writer =
                new BufferedWriter(
                    new OutputStreamWriter(new FileOutputStream(file), StandardCharsets.UTF_8))) {
                writer.write(ShowProofStatistics.getCSVStatisticsMessage(proof));
            }
        } catch (IOException e) {
            LOGGER.error("Failed to write proof stats", e);
        }
        // Says true if all Proofs have succeeded,
        // or false if there is at least one open Proof
        return proof.openGoals().size() == 0;
    }

    @Override
    public TermLabelVisibilityManager getTermLabelVisibilityManager() {
        return null;
    }
}
