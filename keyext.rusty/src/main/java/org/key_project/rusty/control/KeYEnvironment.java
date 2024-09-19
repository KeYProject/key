/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.control;

import java.io.File;
import java.util.List;
import java.util.Properties;
import java.util.function.Consumer;

import org.key_project.rusty.Services;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.io.AbstractProblemLoader;
import org.key_project.rusty.proof.io.AbstractProblemLoader.ReplayResult;
import org.key_project.rusty.proof.io.ProblemLoaderException;
import org.key_project.rusty.proof.io.SingleThreadProblemLoader;

/**
 * Instances of this class are used to collect and access all relevant information for verification
 * with KeY.
 *
 * @author Martin Hentschel
 */
public class KeYEnvironment {
    /**
     * The loaded project.
     */
    private final InitConfig initConfig;

    /**
     * An optional {@link Proof} which was loaded by the specified proof file.
     */
    private final Proof loadedProof;

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
     * @param initConfig The loaded project.
     */
    public KeYEnvironment(InitConfig initConfig, Proof loadedProof, ReplayResult replayResult) {
        this.initConfig = initConfig;
        this.loadedProof = loadedProof;
        this.replayResult = replayResult;
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
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@code MainWindow} is not involved in the whole process.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param includes Optional includes to consider.
     * @param poPropertiesToForce Some optional PO {@link Properties} to force.
     * @param callbackProofLoaded An optional callback (called when the proof is loaded, before
     *        replay)
     * @param forceNewProfileOfNewProofs {@code} true
     *        {@code AbstractProblemLoader.profileOfNewProofs} will be used as {@link Profile} of
     *        new proofs, {@code false} {@link Profile} specified by problem file will be used for
     *        new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment load(Profile profile, File location,
            List<File> includes,
            Properties poPropertiesToForce,
            Consumer<Proof> callbackProofLoaded,
            boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
        AbstractProblemLoader loader = null;
        try {
            loader = new SingleThreadProblemLoader(location, includes,
                profile, null);
            if (callbackProofLoaded != null) {
                loader.load(callbackProofLoaded);
            } else {
                loader.load();
            }
        } catch (ProblemLoaderException e) {
            if (loader.getProof() != null) {
                loader.getProof().dispose();
            }
            // rethrow that exception
            throw e;
        } catch (Throwable e) {
            if (loader != null && loader.getProof() != null) {
                loader.getProof().dispose();
            }
            throw new ProblemLoaderException(loader, e);
        }
        InitConfig initConfig = loader.getInitConfig();

        return new KeYEnvironment(initConfig, loader.getProof(),
            loader.getResult());
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@code MainWindow} is not involved in the whole process.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param includes Optional includes to consider.
     * @param poPropertiesToForce Some optional PO {@link Properties} to force.
     * @param forceNewProfileOfNewProofs {@code} true
     *        {@code AbstractProblemLoader.profileOfNewProofs} will be used as {@link Profile} of
     *        new proofs, {@code false} {@link Profile} specified by problem file will be used for
     *        new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment load(Profile profile, File location,
            List<File> includes,
            Properties poPropertiesToForce,
            boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
        return load(profile, location, includes, poPropertiesToForce,
            null, forceNewProfileOfNewProofs);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@code MainWindow} is not involved in the whole process.
     *
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param includes Optional includes to consider.
     * @param forceNewProfileOfNewProofs {@code} true
     *        {@code AbstractProblemLoader.profileOfNewProofs} will be used as
     *        {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file
     *        will be used for new proofs.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment load(Profile profile, File location,
            List<File> includes,
            boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
        return load(profile, location, includes, null,
            forceNewProfileOfNewProofs);
    }

    /**
     * Loads the given location and returns all required references as {@link KeYEnvironment}. The
     * {@code MainWindow} is not involved in the whole process.
     *
     * @param location The location to load.
     * @param includes Optional includes to consider.
     * @return The {@link KeYEnvironment} which contains all references to the loaded location.
     * @throws ProblemLoaderException Occurred Exception
     */
    public static KeYEnvironment load(File location,
            List<File> includes)
            throws ProblemLoaderException {
        return load(null, location, includes, false);
    }

    public static KeYEnvironment load(File keyFile)
            throws ProblemLoaderException {
        return load(keyFile, null);
    }

    public void dispose() {
        // TODO
    }
}
