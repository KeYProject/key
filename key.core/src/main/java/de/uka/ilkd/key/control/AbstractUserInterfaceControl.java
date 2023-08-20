/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.function.Consumer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;

import org.slf4j.LoggerFactory;

/**
 * Provides a basic implementation of {@link UserInterfaceControl}.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractUserInterfaceControl
        implements UserInterfaceControl, ProblemLoaderControl, ProverTaskListener {
    private static final org.slf4j.Logger LOGGER =
        LoggerFactory.getLogger(AbstractUserInterfaceControl.class);
    private int numOfInvokedMacros = 0;

    /**
     * The registered {@link ProverTaskListener}.
     */
    private final List<ProverTaskListener> proverTaskListener =
        new LinkedList<>();

    /**
     * Constructor.
     */
    public AbstractUserInterfaceControl() {
        addProverTaskListener(new ProofMacroListenerAdapter());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addProverTaskListener(ProverTaskListener ptl) {
        if (ptl != null) {
            proverTaskListener.add(ptl);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeProverTaskListener(ProverTaskListener ptl) {
        if (ptl != null) {
            proverTaskListener.remove(ptl);
        }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskStarted(TaskStartedInfo)} to all listener.
     *
     * @param info the {@link TaskStartedInfo} containing general information about the task that is
     *        just about to start
     */
    protected void fireTaskStarted(TaskStartedInfo info) {
        ProverTaskListener[] listener =
            proverTaskListener.toArray(new ProverTaskListener[0]);
        for (ProverTaskListener l : listener) {
            l.taskStarted(info);
        }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskProgress(int)} to all listener.
     *
     * @param position The current position.
     */
    protected void fireTaskProgress(int position) {
        ProverTaskListener[] listener =
            proverTaskListener.toArray(new ProverTaskListener[0]);
        for (ProverTaskListener l : listener) {
            l.taskProgress(position);
        }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskFinished(TaskFinishedInfo)} to all listener.
     *
     * @param info The {@link TaskFinishedInfo}.
     */
    protected void fireTaskFinished(TaskFinishedInfo info) {
        try {
            ProverTaskListener[] listener =
                proverTaskListener.toArray(new ProverTaskListener[0]);
            for (ProverTaskListener l : listener) {
                l.taskFinished(info);
            }
        } catch (Exception e) {
            LOGGER.error("failed to fire task finished event ", e);
        }
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        fireTaskStarted(info);
    }

    @Override
    public void taskProgress(int position) {
        fireTaskProgress(position);
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        fireTaskFinished(info);
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
    public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate) {
        // Nothing to do
    }

    public boolean isAtLeastOneMacroRunning() {
        return numOfInvokedMacros != 0;
    }

    protected void macroStarted(TaskStartedInfo info) {
        numOfInvokedMacros++;
    }

    protected synchronized void macroFinished(final ProofMacroFinishedInfo info) {
        if (numOfInvokedMacros > 0) {
            numOfInvokedMacros--;
        } else {
            LOGGER.warn("Number of running macros became negative.");
        }
    }

    private class ProofMacroListenerAdapter implements ProverTaskListener {

        @Override
        public void taskStarted(TaskStartedInfo info) {
            if (TaskStartedInfo.TaskKind.Macro == info.getKind()
                    && !info.getMessage().contains(ProverCore.PROCESSING_STRATEGY)) {
                macroStarted(info);
            }
        }

        @Override
        public void taskProgress(int position) {
            // not needed yet
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            if (info instanceof ProofMacroFinishedInfo) {
                macroFinished((ProofMacroFinishedInfo) info);
            }
        }
    }

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
            loader = new SingleThreadProblemLoader(file, classPath, bootClassPath, includes,
                profile, forceNewProfileOfNewProofs, this, false, poPropertiesToForce);
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
        ProblemInitializer pi = new ProblemInitializer(this, new Services(profile), this);
        return pi;
    }

    @Override
    public void loadingStarted(AbstractProblemLoader loader) {
    }

    @Override
    public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer,
            ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
        if (proofList != null) {
            // avoid double registration at spec repos as that is done already earlier in
            // createProof
            // the UI method should just do the necessarily UI registrations
            createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList,
                loader.getInitConfig());
        }
    }
}
