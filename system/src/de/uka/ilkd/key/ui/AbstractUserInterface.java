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

import java.beans.PropertyChangeSupport;
import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.Debug;

public abstract class AbstractUserInterface implements UserInterface {

   /**
    * The used {@link PropertyChangeSupport}.
    */
    private final PropertyChangeSupport pcs = new PropertyChangeSupport(this);

    private ProofMacro autoMacro = new SkipMacro();

    protected ProblemLoader getProblemLoader(File file, List<File> classPath,
                                             File bootClassPath, KeYMediator mediator) {
        final ProblemLoader pl =
                new ProblemLoader(file, classPath, bootClassPath,
                                  AbstractProfile.getDefaultProfile(), mediator, true);
        pl.addTaskListener(this);
        return pl;
    }

    @Override
    public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        app = forced? app.forceInstantiate(goal): app.tryToInstantiate(goal);
        // cannot complete that app
        return app.complete() ? app : null;
    }

    public void setMacro(ProofMacro macro) {
        assert macro != null;
        this.autoMacro = macro;
    }

    public ProofMacro getMacro() {
        return this.autoMacro;
    }

    protected abstract String getMacroConsoleOutput();

    public boolean macroChosen() {
        return !(getMacro() instanceof SkipMacro);
    }

    @Override
    public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput, 
          ProofAggregate proofList, InitConfig initConfig) {
       final ProofEnvironment env = new ProofEnvironment(initConfig); 
       env.addProofEnvironmentListener(this);
       env.registerProof(proofOblInput, proofList);
       return env;
    }

   public boolean applyMacro() {
        assert macroChosen();
        if (getMacro().canApplyTo(getMediator(), null)) {
            System.out.println(getMacroConsoleOutput());
            try {
                getMediator().stopInterface(true);
                getMediator().setInteractive(false);
                getMacro().applyTo(getMediator(), null, this);
                getMediator().setInteractive(true);
                getMediator().startInterface(true);
            } catch(InterruptedException ex) {
                Debug.out("Proof macro has been interrupted:");
                Debug.out(ex);
            } finally {
                Proof proof = getMediator().getSelectedProof();
                TaskFinishedInfo info =
                        new DefaultTaskFinishedInfo(getMacro(), null, proof, proof.getAutoModeTime(),
                                                    proof.countNodes(), proof.openGoals().size());
                taskFinished(info);
            }
            return true;
        } else {
            System.out.println(getMacro().getClass().getSimpleName() + " not applicable!");
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public DefaultProblemLoader load(Profile profile,
                                     File file,
                                     List<File> classPath,
                                     File bootClassPath) throws ProblemLoaderException {
       DefaultProblemLoader loader = null;
       try {
          getMediator().stopInterface(true);
          loader = new DefaultProblemLoader(file, classPath, bootClassPath, profile, getMediator(), false);
          loader.load();
          return loader;
       }
       catch (ProblemLoaderException e) {
          if (loader != null && loader.getProof() != null) {
             loader.getProof().dispose();
          }
          throw e;
       }
       finally {
          getMediator().startInterface(true);
       }
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
    public void startAndWaitForAutoMode(Proof proof) {
       startAutoMode(proof);
       waitWhileAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAutoMode(Proof proof) {
       KeYMediator mediator = getMediator();
       mediator.setProof(proof);
       mediator.startAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
       KeYMediator mediator = getMediator();
       mediator.setProof(proof);
       mediator.startAutoMode(goals);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void stopAutoMode() {
       getMediator().stopAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void waitWhileAutoMode() {
       while (getMediator().autoMode()) { // Wait until auto mode has stopped.
          try {
             Thread.sleep(100);
          }
          catch (InterruptedException e) {
          }
       }
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
}