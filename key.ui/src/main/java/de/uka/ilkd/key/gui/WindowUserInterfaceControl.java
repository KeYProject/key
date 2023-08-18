/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.mergerule.MergeRuleCompletion;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.MediatorProofControl;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ThreadUtilities;

import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Implementation of {@link UserInterfaceControl} which controls the {@link MainWindow} with the
 * typical user interface of KeY.
 *
 * @author Mattias Ulbrich
 */
public class WindowUserInterfaceControl extends AbstractMediatorUserInterfaceControl {
    private static final Logger LOGGER = LoggerFactory.getLogger(WindowUserInterfaceControl.class);

    private final MainWindow mainWindow;

    private final LinkedList<InteractiveRuleApplicationCompletion> completions =
        new LinkedList<>();

    public WindowUserInterfaceControl(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        completions.add(new FunctionalOperationContractCompletion());
        completions.add(new DependencyContractCompletion());
        completions.add(new LoopInvariantRuleCompletion());
        completions.add(new BlockContractInternalCompletion(mainWindow));
        completions.add(new BlockContractExternalCompletion(mainWindow));
        completions.add(MergeRuleCompletion.INSTANCE);
    }

    @Override
    protected MediatorProofControl createProofControl() {
        return new MediatorProofControl(this) {
            /**
             * {@inheritDoc}
             */
            @Override
            public boolean isAutoModeSupported(Proof proof) {
                return super.isAutoModeSupported(proof)
                        && mainWindow.getProofList().containsProof(proof);
            }
        };
    }

    /**
     * loads the problem or proof from the given file
     *
     * @param file the File with the problem description or the proof
     * @param classPath the class path entries to use.
     * @param bootClassPath the boot class path to use.
     */
    public void loadProblem(File file, List<File> classPath, File bootClassPath,
            List<File> includes) {
        mainWindow.addRecentFile(file.getAbsolutePath());
        ProblemLoader problemLoader =
            getProblemLoader(file, classPath, bootClassPath, includes, getMediator());
        problemLoader.runAsynchronously();
    }

    @Override
    public void loadProblem(File file) {
        loadProblem(file, null, null, null);
    }

    @Override
    public void loadProofFromBundle(File proofBundle, File proofFilename) {
        mainWindow.addRecentFile(proofBundle.getAbsolutePath());
        ProblemLoader problemLoader =
            getProblemLoader(proofBundle, null, null, null, getMediator());
        problemLoader.setProofPath(proofFilename);
        problemLoader.runAsynchronously();
    }

    @Override
    public void progressStarted(Object sender) {
        mainWindow.getMediator().stopInterface(true);
    }

    @Override
    public void progressStopped(Object sender) {
        // no need to call startInterface(), will be done by ProblemLoader once loading is done
    }

    @Override
    public void reportException(Object sender, ProofOblInput input, Exception e) {
        reportStatus(sender, input.name() + " failed");
    }

    @Override
    public void reportStatus(Object sender, String status, int progress) {
        mainWindow.setStatusLine(status, progress);
    }

    @Override
    public void reportStatus(Object sender, String status) {
        mainWindow.setStatusLine(status);
    }

    @Override
    public void resetStatus(Object sender) {
        mainWindow.setStandardStatusLine();
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        super.taskFinished(info);
        // ensure all UI modifying operations are done on the UI thread
        SwingUtilities.invokeLater(() -> taskFinishedInternal(info));
    }

    private void taskFinishedInternal(TaskFinishedInfo info) {
        if (info != null && info.getSource() instanceof ProverCore) {
            if (!isAtLeastOneMacroRunning()) {
                resetStatus(this);
            }
            ApplyStrategyInfo result = (ApplyStrategyInfo) info.getResult();

            Proof proof = info.getProof();
            if (proof != null && !proof.isDisposed() && !proof.closed()
                    && mainWindow.getMediator().getSelectedProof() == proof) {
                Goal g = result.nonCloseableGoal();
                if (g == null) {
                    g = proof.openGoals().head();
                }
                mainWindow.getMediator().goalChosen(g);
                if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
                    // iff Stop on non-closeable Goal is selected a little
                    // popup is generated and proof is stopped
                    AutoDismissDialog dialog = new AutoDismissDialog(
                        "Couldn't close Goal Nr. " + g.node().serialNr() + " automatically");
                    dialog.show();
                }
            }
            mainWindow.displayResults(info.toString());
        } else if (info != null && info.getSource() instanceof ProofMacro) {
            if (!isAtLeastOneMacroRunning()) {
                resetStatus(this);
                assert info instanceof ProofMacroFinishedInfo;
                Proof proof = info.getProof();
                if (proof != null && !proof.closed()
                        && mainWindow.getMediator().getSelectedProof() == proof) {
                    Goal g = proof.openGoals().head();
                    mainWindow.getMediator().goalChosen(g);
                    if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
                        // iff Stop on non-closeable Goal is selected a little
                        // popup is generated and proof is stopped
                        AutoDismissDialog dialog = new AutoDismissDialog(
                            "Couldn't close Goal Nr. " + g.node().serialNr() + " automatically");
                        dialog.show();
                    }
                }
            }
        } else if (info != null && info.getSource() instanceof ProblemLoader) {
            resetStatus(this);
            Throwable result = (Throwable) info.getResult();
            if (info.getResult() != null) {
                LOGGER.error("", result);
                IssueDialog.showExceptionDialog(mainWindow, result);
            } else if (getMediator().getUI().isSaveOnly()) {
                mainWindow.displayResults("Finished Saving!");
            } else {
                KeYMediator mediator = mainWindow.getMediator();
                mediator.getNotationInfo().refresh(mediator.getServices());
                ProblemLoader problemLoader = (ProblemLoader) info.getSource();
                if (problemLoader.hasProofScript()) {
                    Pair<String, Location> scriptAndLoc;
                    try {
                        scriptAndLoc = problemLoader.readProofScript();
                        ProofScriptWorker psw = new ProofScriptWorker(mainWindow.getMediator(),
                            scriptAndLoc.first, scriptAndLoc.second);
                        psw.init();
                        psw.execute();
                    } catch (ProofInputException e) {
                        LOGGER.warn("Failed to load proof", e);
                    }
                } else if (macroChosen()) {
                    applyMacro();
                }
            }
        } else {
            resetStatus(this);
            if (info != null && !info.toString().isEmpty()) {
                mainWindow.displayResults(info.toString());
            }
        }
        // this seems to be a good place to free some memory
        Runtime.getRuntime().gc();
    }

    protected boolean inStopAtFirstUncloseableGoalMode(Proof proof) {
        return proof.getSettings().getStrategySettings().getActiveStrategyProperties()
                .getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    @Override
    public void taskProgress(int position) {
        super.taskProgress(position);
        mainWindow.getStatusLine().setProgress(position);

    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        super.taskStarted(info);
        mainWindow.setStatusLine(info.getMessage(), info.getSize());
    }

    @Override
    public void setMaximum(int maximum) {
        mainWindow.getStatusLine().setProgressBarMaximum(maximum);
    }

    @Override
    public void setProgress(int progress) {
        mainWindow.getStatusLine().setProgress(progress);
    }

    @Override
    public void notifyAutoModeBeingStarted() {
        mainWindow.setCursor(new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR));
        super.notifyAutoModeBeingStarted();
    }

    @Override
    public void notifyAutomodeStopped() {
        mainWindow.setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
        super.notifyAutomodeStopped();
    }

    @Override
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models, Goal goal) {
        new TacletMatchCompletionDialog(mainWindow, models, goal, mainWindow.getMediator());
    }

    @Override
    public boolean confirmTaskRemoval(String string) {
        int answer = JOptionPane.showConfirmDialog(MainWindow.getInstance(), string,
            "Abandon Proof", JOptionPane.YES_NO_OPTION);
        return answer == JOptionPane.YES_OPTION;
    }

    @Override
    public void openExamples() {
        mainWindow.openExamples();
    }

    @Override
    public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        if (mainWindow.getMediator().isInAutoMode()) {
            return AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, forced);
        }
        IBuiltInRuleApp result = app;
        for (InteractiveRuleApplicationCompletion compl : completions) {
            if (compl.canComplete(app)) {
                result = compl.complete(app, goal, forced);
                break;
            }
        }
        return (result != null && result.complete()) ? result : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYMediator getMediator() {
        return mainWindow.getMediator();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractProblemLoader load(Profile profile, File file, List<File> classPath,
            File bootClassPath, List<File> includes, Properties poPropertiesToForce,
            boolean forceNewProfileOfNewProofs, Consumer<Proof> callback)
            throws ProblemLoaderException {
        if (file != null) {
            mainWindow.getRecentFiles().addRecentFile(file.getAbsolutePath());
        }
        try {
            getMediator().stopInterface(true);
            return super.load(profile, file, classPath, bootClassPath, includes,
                poPropertiesToForce, forceNewProfileOfNewProofs, callback);
        } finally {
            getMediator().startInterface(true);
        }
    }

    /**
     * Save proof in file. If autoSave is on, this will potentially overwrite already existing proof
     * files with the same name. Otherwise the save dialog pops up. For loaded proofs both are
     * turned off by default, i.e. only manual saving is possible, and the save dialog never pops up
     * automatically (except for hitting the "Save ..." or "Save current proof" button).
     *
     * @param proof the proof to be saved
     * @param fileExtension the respective file extension
     * @return the saved proof as a file
     */
    public File saveProof(Proof proof, String fileExtension) {
        final MainWindow mainWindow = MainWindow.getInstance();
        final KeYFileChooser fc = KeYFileChooser.getFileChooser("Choose filename to save proof");
        fc.setFileFilter(KeYFileChooser.DEFAULT_FILTER);

        Pair<File, String> f = fileName(proof, fileExtension);
        final int result = fc.showSaveDialog(mainWindow, f.first, f.second);
        File file = null;
        if (result == JFileChooser.APPROVE_OPTION) { // saved
            file = fc.getSelectedFile();
            final String filename = file.getAbsolutePath();
            ProofSaver saver;
            if (fc.useCompression()) {
                saver = new GZipProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION);
            } else {
                saver = new ProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION);
            }
            String errorMsg;
            try {
                getMediator().stopInterface(true);
                errorMsg = saver.save();
            } catch (IOException e) {
                errorMsg = e.toString();
            } finally {
                getMediator().startInterface(true);
            }
            if (errorMsg != null) {
                mainWindow.notify(
                    new GeneralFailureEvent("Saving Proof failed.\n Error: " + errorMsg));
            } else {
                proof.setProofFile(file);
            }
        }
        return file;
    }

    /**
     * Saves the proof as a bundle, i.e., as a zip archive containing all dependencies (Java
     * sources, classpath and bootclasspath if present, other included key files, e.g., user-defined
     * taclets).
     *
     * @param proof the proof to save
     */
    public void saveProofBundle(Proof proof) {
        final MainWindow mainWindow = MainWindow.getInstance();
        final KeYFileChooser fileChooser =
            KeYFileChooser.getFileChooser("Choose filename to save proof");
        fileChooser.setFileFilter(KeYFileChooser.PROOF_BUNDLE_FILTER);

        Pair<File, String> f = fileName(proof, ".zproof");
        final int result = fileChooser.showSaveDialog(mainWindow, f.first, f.second);
        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fileChooser.getSelectedFile();
            ProofSaver saver = new ProofBundleSaver(proof, file);

            String errorMsg;
            try {
                errorMsg = saver.save();
            } catch (IOException e) {
                errorMsg = e.toString();
            }
            if (errorMsg != null) {
                mainWindow.notify(
                    new GeneralFailureEvent("Saving Proof failed.\n Error: " + errorMsg));
            } else {
                proof.setProofFile(file);
            }
        }
    }

    protected static Pair<File, String> fileName(Proof proof, String fileExtension) {
        // TODO: why do we use GUI components here?
        final KeYFileChooser jFC = KeYFileChooser.getFileChooser("Choose filename to save proof");

        File selectedFile = null;
        if (proof != null) {
            selectedFile = proof.getProofFile();
        }
        // Suggest default file name if required
        final String defaultName;
        if (selectedFile == null) {
            // Remove space
            var name = proof.name().toString();
            var prefix = "Taclet: ";
            if (name.startsWith(prefix)) {
                name = "Taclet:" + name.substring(prefix.length());
            }
            defaultName = MiscTools.toValidFileName(name) + fileExtension;
            selectedFile = new File(jFC.getCurrentDirectory(), defaultName);
        } else if (selectedFile.getName().endsWith(".proof") && fileExtension.equals(".proof")) {
            defaultName = selectedFile.getName();
        } else {
            String proofName = proof.name().toString();
            if (proofName.endsWith(".key")) {
                proofName = proofName.substring(0, proofName.lastIndexOf(".key"));
            } else if (proofName.endsWith(".proof")) {
                proofName = proofName.substring(0, proofName.lastIndexOf(".proof"));
            }
            defaultName = MiscTools.toValidFileName(proofName) + fileExtension;
            selectedFile = new File(selectedFile.getParentFile(), defaultName);
        }
        return new Pair<>(selectedFile, defaultName);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void proofDisposing(final ProofDisposedEvent e) {
        super.proofDisposing(e);
        // Remove proof from user interface
        ThreadUtilities.invokeAndWait(() -> mainWindow.getProofList().removeProof(e.getSource()));
    }

    @Override
    public boolean selectProofObligation(InitConfig initConfig) {
        return ProofManagementDialog.showInstance(initConfig);
    }

    @Override
    public void registerProofAggregate(ProofAggregate pa) {
        super.registerProofAggregate(pa);
        mainWindow.addProblem(pa);
        mainWindow.setStandardStatusLine();
    }

    @Override
    public void loadingStarted(AbstractProblemLoader loader) {
        getMediator().stopInterface(true);
        super.loadingStarted(loader);
    }

    @Override
    public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer,
            ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
        super.loadingFinished(loader, poContainer, proofList, result);
        if (proofList != null) {
            if (result != null) {
                if ("".equals(result.getStatus())) {
                    this.resetStatus(this);
                } else {
                    this.reportStatus(this, result.getStatus());
                }
                getMediator().getSelectionModel().setSelectedNode(result.getNode());
                if (result.hasErrors()) {
                    throw new ProblemLoaderException(loader,
                        "Proof could only be loaded partially.\n" + "In summary "
                            + result.getErrorList().size()
                            + " not loadable rule application(s) have been detected.\n"
                            + "The first one:\n" + result.getErrorList().get(0).getMessage(),
                        result.getErrorList().get(0));
                }
            } else {
                // should never happen as replay always returns a result object
                // TODO (DS): Why is it then there? If this happens, we will get\\
                // a NullPointerException just a line below...
                getMediator().getSelectionModel().setSelectedNode(loader.getProof().root());
            }
        }
        getMediator().resetNrGoalsClosedByHeuristics();
        if (poContainer != null && poContainer.getProofOblInput() instanceof KeYUserProblemFile) {
            ((KeYUserProblemFile) poContainer.getProofOblInput()).close();
        }
    }



    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment} with
     * KeY's {@link MainWindow}.
     *
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already
     *        visible?
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    // public static KeYEnvironment<WindowUserInterfaceControl> loadInMainWindow(File location,
    // List<File> classPaths,
    // File bootClassPath,
    // List<File> includes,
    // boolean makeMainWindowVisible) throws ProblemLoaderException {
    // return loadInMainWindow(null, location, classPaths, bootClassPath, includes, false,
    // makeMainWindowVisible);
    // }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment} with
     * KeY's {@link MainWindow}.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already
     *        visible?
     * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as
     *        {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file
     *        will be used for new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment<WindowUserInterfaceControl> loadInMainWindow(Profile profile,
            File location, List<File> classPaths, File bootClassPath, List<File> includes,
            boolean forceNewProfileOfNewProofs, boolean makeMainWindowVisible)
            throws ProblemLoaderException {
        MainWindow main = MainWindow.getInstance();
        if (makeMainWindowVisible && !main.isVisible()) {
            main.setVisible(true);
        }
        AbstractProblemLoader loader = main.getUserInterface().load(profile, location, classPaths,
            bootClassPath, includes, null, forceNewProfileOfNewProofs, null);
        InitConfig initConfig = loader.getInitConfig();
        return new KeYEnvironment<>(main.getUserInterface(), initConfig,
            loader.getProof(), loader.getProofScript(), loader.getResult());
    }

    @Override
    public void notify(NotificationEvent event) {
        mainWindow.notify(event);
    }

    @Override
    public void reportWarnings(ImmutableSet<PositionedString> warnings) {
        IssueDialog.showWarningsIfNecessary(mainWindow, warnings);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TermLabelVisibilityManager getTermLabelVisibilityManager() {
        return mainWindow.getVisibleTermLabels();
    }

    @Override
    public void showIssueDialog(Collection<PositionedString> issues) {
        final var set = issues.stream()
                .map(it -> new PositionedIssueString(
                    it.text, it.location, ""))
                .collect(Collectors.toSet());
        var dialog = new IssueDialog(mainWindow, "Issues", set, true, null);
        dialog.setVisible(true);
    }
}
