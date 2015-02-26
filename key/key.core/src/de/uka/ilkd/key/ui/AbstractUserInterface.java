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

package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public abstract class AbstractUserInterface implements UserInterface {

    private ProofMacro autoMacro = new SkipMacro();
    protected boolean saveOnly = false;

    private ProverTaskListener pml = null;

    @Override
    public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        app = forced? app.forceInstantiate(goal): app.tryToInstantiate(goal);
        // cannot complete that app
        return app.complete() ? app : null;
    }

    public void setSaveOnly(boolean s) {
        this.saveOnly = s;
    }
    
    public boolean isSaveOnly() {
        return this.saveOnly;
    }

    public void setMacro(ProofMacro macro) {
        assert macro != null;
        this.autoMacro = macro;
    }

    public ProofMacro getMacro() {
        return this.autoMacro;
    }

    public boolean macroChosen() {
        return !(getMacro() instanceof SkipMacro);
    }

    @Override
    public final ProverTaskListener getListener() {
        if (this.pml == null) {
            this.pml = new ProofMacroListenerAdapter();
        }
        return new CompositePTListener(this, pml);
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
     * {@inheritDoc}
     */
    @Override
    public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate) {
       // Nothing to do
    }
 
    /**
     * {@inheritDoc}
     */
    @Override
    public void notifyAutoModeBeingStarted() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void notifyAutomodeStopped() {
    }

    @Override
    public void proofUnregistered(ProofEnvironmentEvent event) {
       if (event.getSource().getProofs().isEmpty()) {
          event.getSource().removeProofEnvironmentListener(this);
       }
    }

    protected abstract void macroStarted(String message, int size);
    protected abstract void macroFinished(TaskFinishedInfo info);


    private class ProofMacroListenerAdapter implements ProverTaskListener {

        @Override
        public void taskStarted(String message, int size) {
            macroStarted(message, size);
        }

        @Override
        public void taskProgress(int position) {
            // not needed yet
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            macroFinished(info);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isAutoModeSupported(Proof proof) {
       return true; // All proofs are supported.
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractProblemLoader load(Profile profile,
                                     File file,
                                     List<File> classPath,
                                     File bootClassPath,
                                     Properties poPropertiesToForce,
                                     boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
       AbstractProblemLoader loader = null;
       try {
          loader = new SingleThreadProblemLoader(file, classPath, bootClassPath, profile, forceNewProfileOfNewProofs,
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

    @Override
    public ProblemInitializer createProblemInitializer(Profile profile) {
        ProblemInitializer pi = new ProblemInitializer(this, new Services(profile), this);
        return pi;
    }

    @Override
    public void loadingStarted() {
    }

    @Override
    public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer, ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
       if (proofList != null) {
          // avoid double registration at specrepos as that is done already earlier in createProof
          // the UI method should just do the necessarily UI registrations
          createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList, loader.getInitConfig());
       }
    }

    @Override
    public boolean confirmTaskRemoval(String string) {
        return true;
    }
}