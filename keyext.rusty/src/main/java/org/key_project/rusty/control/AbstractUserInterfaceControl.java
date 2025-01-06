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
import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.init.*;
import org.key_project.rusty.proof.io.AbstractProblemLoader;
import org.key_project.rusty.proof.io.ProblemLoaderControl;
import org.key_project.rusty.proof.io.ProblemLoaderException;
import org.key_project.rusty.proof.io.SingleThreadProblemLoader;
import org.key_project.rusty.proof.mgt.ProofEnvironment;

public abstract class AbstractUserInterfaceControl
        implements UserInterfaceControl, ProblemLoaderControl {
    /**
     * Constructor.
     */
    protected AbstractUserInterfaceControl() {

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Proof createProof(InitConfig initConfig, ProofOblInput input)
            throws ProofInputException {
        ProblemInitializer init = createProblemInitializer(initConfig.getProfile());
        ProofAggregate proofList = init.startProver(initConfig, input);
        createProofEnvironmentAndRegisterProof(input, proofList, initConfig);
        return proofList.getFirstProof();
    }

    /**
     * registers the proof aggregate at the UI
     *
     * @param proofOblInput the {@link ProofOblInput}
     * @param proofList the {@link ProofAggregate}
     * @param initConfig the {@link InitConfig} to be used
     * @return the new {@link ProofEnvironment} where the {@link ProofAggregate} has been registered
     */
    protected abstract ProofEnvironment createProofEnvironmentAndRegisterProof(
            ProofOblInput proofOblInput, ProofAggregate proofList, InitConfig initConfig);

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractProblemLoader load(Profile profile, File file, List<File> classPath,
            File bootClassPath, List<File> includes, Properties poPropertiesToForce,
            boolean forceNewProfileOfNewProofs,
            Consumer<Proof> callback) throws ProblemLoaderException {
        AbstractProblemLoader loader = null;
        try {
            loader = new SingleThreadProblemLoader(file, includes,
                profile, null);
            if (callback != null) {
                loader.load(callback);
            } else {
                loader.load();
            }
            return loader;
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
    }

    /**
     * <p>
     * Creates a new {@link ProblemInitializer} instance which is configured for this
     * {@link UserInterfaceControl}.
     * </p>
     * <p>
     * This method is used by nearly all Eclipse based product that uses KeY.
     * </p>
     *
     * @param profile The {@link Profile} to use.
     * @return The instantiated {@link ProblemInitializer}.
     */
    protected ProblemInitializer createProblemInitializer(Profile profile) {
        return new ProblemInitializer(new Services(profile));
    }
}
