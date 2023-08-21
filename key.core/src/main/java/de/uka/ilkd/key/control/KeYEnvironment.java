/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import java.io.File;
import java.util.List;
import java.util.Properties;
import java.util.function.Consumer;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Pair;

/**
 * Instances of this class are used to collect and access all relevant information for verification
 * with KeY.
 *
 * @author Martin Hentschel
 */
public class KeYEnvironment<U extends UserInterfaceControl> {
    /**
     * The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
     */
    private final U ui;

    /**
     * The loaded project.
     */
    private final InitConfig initConfig;

    /**
     * An optional {@link Proof} which was loaded by the specified proof file.
     */
    private final Proof loadedProof;

    /**
     * An optional field denoting a script contained in the proof file.
     */
    private final Pair<String, Location> proofScript;

    /**
     * Indicates that this {@link KeYEnvironment} is disposed.
     */
    private boolean disposed;

    /**
     * The {@link ReplayResult} if available.
     */
    private final ReplayResult replayResult;

    /**
     * Constructor
     *
     * @param ui The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
     * @param initConfig The loaded project.
     */
    public KeYEnvironment(U ui, InitConfig initConfig) {
        this(ui, initConfig, null, null, null);
    }

    /**
     * Constructor
     *
     * @param ui The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
     * @param initConfig The loaded project.
     */
    public KeYEnvironment(U ui, InitConfig initConfig, Proof loadedProof,
            Pair<String, Location> proofScript, ReplayResult replayResult) {
        this.ui = ui;
        this.initConfig = initConfig;
        this.loadedProof = loadedProof;
        this.proofScript = proofScript;
        this.replayResult = replayResult;
    }

    /**
     * Returns the {@link UserInterfaceControl} in which the {@link Proof} is loaded.
     *
     * @return The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
     */
    public U getUi() {
        return ui;
    }

    /**
     * Returns the {@link ProofControl} of {@link #getUi()}.
     *
     * @return The {@link ProofControl} of {@link #getUi()}.
     */
    public ProofControl getProofControl() {
        return ui != null ? ui.getProofControl() : null;
    }

    /**
     * Returns the loaded project.
     *
     * @return The loaded project.
     */
    public InitConfig getInitConfig() {
        return initConfig;
    }

    /**
     * Returns the {@link Services} of {@link #getInitConfig()}.
     *
     * @return The {@link Services} of {@link #getInitConfig()}.
     */
    public Services getServices() {
        return initConfig.getServices();
    }

    /**
     * Returns the used {@link JavaInfo}.
     *
     * @return The used {@link JavaInfo}.
     */
    public JavaInfo getJavaInfo() {
        return getServices().getJavaInfo();
    }

    /**
     * Returns the used {@link SpecificationRepository}.
     *
     * @return The used {@link SpecificationRepository}.
     */
    public SpecificationRepository getSpecificationRepository() {
        return getServices().getSpecificationRepository();
    }

    public Profile getProfile() {
        return getInitConfig().getProfile();
    }

    /**
     * Returns the loaded {@link Proof} if a proof file was loaded.
     *
     * @return The loaded {@link Proof} if available and {@code null} otherwise.
     */
    public Proof getLoadedProof() {
        return loadedProof;
    }

    /**
     * Returns the {@link ReplayResult} if available.
     *
     * @return The {@link ReplayResult} or {@code null} if not available.
     */
    public ReplayResult getReplayResult() {
        return replayResult;
    }

    /**
     * Creates a new {@link Proof} with help of the {@link UserInterfaceControl}.
     *
     * @param input The {@link ProofOblInput} to instantiate {@link Proof} from.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    public Proof createProof(ProofOblInput input) throws ProofInputException {
        return ui.createProof(getInitConfig(), input);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@link MainWindow} is not involved in the whole process.
     *
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment<DefaultUserInterfaceControl> load(File location,
            List<File> classPaths, File bootClassPath, List<File> includes)
            throws ProblemLoaderException {
        return load(null, location, classPaths, bootClassPath, includes, false);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@link MainWindow} is not involved in the whole process.
     *
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment<DefaultUserInterfaceControl> load(File location,
            List<File> classPaths, File bootClassPath, List<File> includes,
            RuleCompletionHandler ruleCompletionHandler) throws ProblemLoaderException {
        return load(null, location, classPaths, bootClassPath, includes, null,
            ruleCompletionHandler, false);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@link MainWindow} is not involved in the whole process.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as
     *        {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file
     *        will be used for new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment<DefaultUserInterfaceControl> load(Profile profile, File location,
            List<File> classPaths, File bootClassPath, List<File> includes,
            boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
        return load(profile, location, classPaths, bootClassPath, includes, null, null,
            forceNewProfileOfNewProofs);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@link MainWindow} is not involved in the whole process.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param poPropertiesToForce Some optional PO {@link Properties} to force.
     * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
     * @param forceNewProfileOfNewProofs {@code} true
     *        {@link AbstractProblemLoader#profileOfNewProofs} will be used as {@link Profile} of
     *        new proofs, {@code false} {@link Profile} specified by problem file will be used for
     *        new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment<DefaultUserInterfaceControl> load(Profile profile, File location,
            List<File> classPaths, File bootClassPath, List<File> includes,
            Properties poPropertiesToForce, RuleCompletionHandler ruleCompletionHandler,
            boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
        return load(profile, location, classPaths, bootClassPath, includes, poPropertiesToForce,
            ruleCompletionHandler,
            null, forceNewProfileOfNewProofs);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@link MainWindow} is not involved in the whole process.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param poPropertiesToForce Some optional PO {@link Properties} to force.
     * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
     * @param callbackProofLoaded An optional callback (called when the proof is loaded, before
     *        replay)
     * @param forceNewProfileOfNewProofs {@code} true
     *        {@link AbstractProblemLoader#profileOfNewProofs} will be used as {@link Profile} of
     *        new proofs, {@code false} {@link Profile} specified by problem file will be used for
     *        new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment<DefaultUserInterfaceControl> load(Profile profile, File location,
            List<File> classPaths, File bootClassPath, List<File> includes,
            Properties poPropertiesToForce, RuleCompletionHandler ruleCompletionHandler,
            Consumer<Proof> callbackProofLoaded,
            boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
        DefaultUserInterfaceControl ui = new DefaultUserInterfaceControl(ruleCompletionHandler);
        AbstractProblemLoader loader = ui.load(profile, location, classPaths, bootClassPath,
            includes, poPropertiesToForce, forceNewProfileOfNewProofs, callbackProofLoaded);
        InitConfig initConfig = loader.getInitConfig();

        return new KeYEnvironment<>(ui, initConfig, loader.getProof(),
            loader.getProofScript(), loader.getResult());
    }

    public static KeYEnvironment<DefaultUserInterfaceControl> load(File keyFile)
            throws ProblemLoaderException {
        return load(keyFile, null, null, null);
    }

    /**
     * Disposes this {@link KeYEnvironment}.
     */
    public void dispose() {
        if (loadedProof != null && !loadedProof.isDisposed()) {
            loadedProof.dispose();
        }
        disposed = true;
    }

    /**
     * Checks if this {@link KeYEnvironment} is disposed meaning that {@link #dispose()} was already
     * executed at least once.
     *
     * @return {@code true} disposed, {@code false} not disposed and still functionable.
     */
    public boolean isDisposed() {
        return disposed;
    }

    public Pair<String, Location> getProofScript() {
        return proofScript;
    }

}
