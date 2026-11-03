/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.control;

import java.nio.file.Path;
import java.util.List;
import java.util.Objects;
import java.util.Properties;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicInteger;
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

import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskFinishedInfo;
import org.key_project.prover.engine.TaskStartedInfo;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Provides a basic implementation of {@link UserInterfaceControl}.
 *
 * @author Martin Hentschel
 */
@NullMarked
public abstract class AbstractUserInterfaceControl
        implements UserInterfaceControl, ProblemLoaderControl, ProverTaskListener {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(AbstractUserInterfaceControl.class);
    protected AtomicInteger numOfInvokedMacros = new AtomicInteger(0);

    /**
     * The registered {@link ProverTaskListener}.
     */
    private final List<ProverTaskListener> proverTaskListener = new CopyOnWriteArrayList<>();

    /**
     * The listener registration operates on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here because the listener only ever
     * reacts to later events, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    protected AbstractUserInterfaceControl() {
        addProverTaskListener(new ProofMacroListenerAdapter());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addProverTaskListener(@Nullable ProverTaskListener ptl) {
        if (ptl != null) {
            proverTaskListener.add(ptl);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeProverTaskListener(@Nullable ProverTaskListener ptl) {
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
        synchronized (proverTaskListener) {
            for (ProverTaskListener l : proverTaskListener) {
                l.taskStarted(info);
            }
        }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskProgress(int)} to all listener.
     *
     * @param position The current position.
     */
    protected void fireTaskProgress(int position) {
        synchronized (proverTaskListener) {
            for (ProverTaskListener l : proverTaskListener) {
                l.taskProgress(position);
            }
        }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskFinished(TaskFinishedInfo)} to all listener.
     *
     * @param info The {@link TaskFinishedInfo}.
     */
    protected void fireTaskFinished(TaskFinishedInfo info) {
        try {
            synchronized (proverTaskListener) {
                for (ProverTaskListener l : proverTaskListener) {
                    l.taskFinished(info);
                }
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
        ProblemInitializer init = createProblemInitializer(
            Objects.requireNonNull(initConfig.getProfile(),
                "Proof creation requires a profile in the init config"));
        ProofAggregate proofList = init.startProver(initConfig, input);
        createProofEnvironmentAndRegisterProof(input, proofList, initConfig);
        Proof proof = proofList.getFirstProof();
        if (proof == null) {
            throw new IllegalStateException("Proof obligation did not produce a proof");
        }
        return proof;
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
        return numOfInvokedMacros.getAcquire() != 0;
    }

    protected void macroStarted(TaskStartedInfo info) {
        numOfInvokedMacros.incrementAndGet();
    }

    protected void macroFinished(final ProofMacroFinishedInfo info) {
        if (numOfInvokedMacros.getAcquire() > 0) {
            numOfInvokedMacros.decrementAndGet();
        } else {
            LOGGER.warn("Number of running macros became negative.");
        }
    }

    private class ProofMacroListenerAdapter implements ProverTaskListener {

        @Override
        public void taskStarted(TaskStartedInfo info) {
            if (TaskStartedInfo.TaskKind.Macro == info.kind()
                    && !info.message().contains(ProverCore.PROCESSING_STRATEGY)) {
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
     * <p>
     * A partially-loaded problem's proof is disposed on failure only when it was actually created
     * (checked on the same loader); the dereferences of the (nullable) loaded proof are suppressed
     * with a scoped key.
     * <p>
     * The loader's constructors accept absent values for the optional class path, boot class path,
     * global includes, profile of new proofs and proof-obligation properties (the problem loader
     * treats each as optional, cf. {@link AbstractProblemLoader#setClassPath} and the null-guard on
     * its {@code poPropertiesToForce}); and the failing loader is itself {@code null} when its own
     * construction threw. Passing these values to the loader and exception constructors is
     * suppressed with a scoped key.
     */
    @Override
    @SuppressWarnings({ "nullness:argument.type.incompatible",
        "nullness:dereference.of.nullable" })
    public AbstractProblemLoader load(@Nullable Profile profile, Path file,
            @Nullable List<Path> classPath,
            @Nullable Path bootClassPath, @Nullable List<Path> includes,
            @Nullable Properties poPropertiesToForce,
            boolean forceNewProfileOfNewProofs,
            @Nullable Consumer<Proof> callback) throws ProblemLoaderException {
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
            throw new ProblemLoaderException(loader, "Load failed", e);
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
        return new ProblemInitializer(this, new Services(profile), this);
    }

    @Override
    public void loadingStarted(AbstractProblemLoader loader) {}

    /**
     * {@inheritDoc}
     * <p>
     * The proof list and its proof-obligation container are passed together by the loading
     * pipeline whenever the list is non-null; the dereference of the (nullable) container is
     * suppressed with a scoped key.
     */
    @Override
    @SuppressWarnings("nullness:dereference.of.nullable")
    public void loadingFinished(AbstractProblemLoader loader,
            @Nullable LoadedPOContainer poContainer,
            @Nullable ProofAggregate proofList, @Nullable ReplayResult result)
            throws ProblemLoaderException {
        if (proofList != null) {
            // avoid double registration at spec repos as that is done already earlier in
            // createProof
            // the UI method should just do the necessarily UI registrations
            createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList,
                Objects.requireNonNull(loader.getInitConfig(),
                    "A loaded proof list implies an init config"));
        }
    }
}
