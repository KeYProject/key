// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.control;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.logging.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

/**
 * Provides a basic implementation of {@link UserInterfaceControl}.
 * @author Martin Hentschel
 */
public abstract class AbstractUserInterfaceControl implements UserInterfaceControl, ProblemLoaderControl, ProverTaskListener {
    private int numOfInvokedMacros = 0;
    
    /**
     * The registered {@link ProverTaskListener}.
     */
    private final List<ProverTaskListener> proverTaskListener = new LinkedList<ProverTaskListener>();
    
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
     * Fires the event {@link ProverTaskListener#taskStarted(String, int)} to all listener.
     * @param info the {@link TaskStartedInfo} containing general information about the task that is just about to start
     */
    protected void fireTaskStarted(TaskStartedInfo info) {
       ProverTaskListener[] listener = proverTaskListener.toArray(new ProverTaskListener[proverTaskListener.size()]);
       for (ProverTaskListener l : listener) {
          l.taskStarted(info);
       }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskProgress(int)} to all listener.
     * @param position The current position.
     */
    protected void fireTaskProgress(int position) {
       ProverTaskListener[] listener = proverTaskListener.toArray(new ProverTaskListener[proverTaskListener.size()]);
       for (ProverTaskListener l : listener) {
          l.taskProgress(position);
       }
    }

    /**
     * Fires the event {@link ProverTaskListener#taskFinished(TaskFinishedInfo)} to all listener.
     * @param info The {@link TaskFinishedInfo}.
     */
    protected void fireTaskFinished(TaskFinishedInfo info) {
       ProverTaskListener[] listener = proverTaskListener.toArray(new ProverTaskListener[proverTaskListener.size()]);
       for (ProverTaskListener l : listener) {
          l.taskFinished(info);
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
    public Proof createProof(InitConfig initConfig, ProofOblInput input) throws ProofInputException {
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
    protected abstract ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput, ProofAggregate proofList, InitConfig initConfig);

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
        }
        else { 
            Logger.getLogger(this.getClass().getName(), "Number of running macros became negative.");
        }
    }

    private class ProofMacroListenerAdapter implements ProverTaskListener {

        @Override
        public void taskStarted(TaskStartedInfo info) {
            if (TaskStartedInfo.TaskKind.Macro == info.getKind()
                    && !info.getMessage().contains(ApplyStrategy.PROCESSING_STRATEGY)) {
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
               macroFinished((ProofMacroFinishedInfo)info);
            }
        }
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractProblemLoader load(Profile profile,
                                     File file,
                                     List<File> classPath,
                                     File bootClassPath,
                                     List<File> includes,
                                     Properties poPropertiesToForce,
                                     boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
       AbstractProblemLoader loader = null;
       try {
          loader = new SingleThreadProblemLoader(file, classPath, bootClassPath, includes, profile, forceNewProfileOfNewProofs,
                                                 this, false, poPropertiesToForce);
          loader.load();
          return loader;
       }
       catch(ProblemLoaderException e) {
           if (loader != null && loader.getProof() != null) {
               loader.getProof().dispose();
           }
           // rethrow that exception
           throw e;
       }
       catch (Throwable e) {
           if (loader != null && loader.getProof() != null) {
               loader.getProof().dispose();
           }
           throw new ProblemLoaderException(loader, e);
       }
    }

    /**
     * <p>
     * Creates a new {@link ProblemInitializer} instance which is configured
     * for this {@link UserInterfaceControl}.
     * </p>
     * <p>
     * This method is used by nearly all Eclipse based product that
     * uses KeY.
     * </p>
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
    public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer, ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
       if (proofList != null) {
          // avoid double registration at spec repos as that is done already earlier in createProof
          // the UI method should just do the necessarily UI registrations
          createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList, loader.getInitConfig());
       }
    }
}