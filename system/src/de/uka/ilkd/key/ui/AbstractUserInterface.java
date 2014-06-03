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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.macros.DummyProofMacro;
import de.uka.ilkd.key.gui.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.Debug;

public abstract class AbstractUserInterface implements UserInterface {
   private boolean autoMode;

   /**
    * The used {@link PropertyChangeSupport}.
    */
    private final PropertyChangeSupport pcs = new PropertyChangeSupport(this);

    private ProofMacro autoMacro = new DummyProofMacro();
    protected boolean saveOnly = false;

	protected ProblemLoader getProblemLoader(File file, List<File> classPath,
	                                         File bootClassPath, KeYMediator mediator) {
		final ProblemLoader pl = new ProblemLoader(file, classPath,
		        bootClassPath, AbstractProfile.getDefaultProfile(), mediator);
		pl.addTaskListener(this);
		return pl;
	}

    @Override
    public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
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

    protected abstract String getMacroConsoleOutput();

    public boolean macroChosen() {
        return !(getMacro() instanceof DummyProofMacro);
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
          loader = new DefaultProblemLoader(file, classPath, bootClassPath, profile, getMediator());
          if (isSaveOnly()) {
              loader.saveAll();
          } else {
              loader.load();
          }
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
       return init.startProver(initConfig, input, 0);
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

    @Override
    public boolean isAutoMode() {
        return autoMode;
    }

    @Override
    public void notifyAutoModeBeingStarted() {
       boolean oldValue = isAutoMode();
       autoMode = true;
       firePropertyChange(PROP_AUTO_MODE, oldValue, isAutoMode());
    }

    @Override
    public void notifyAutomodeStopped() {
       boolean oldValue = isAutoMode();
       autoMode = false;
       firePropertyChange(PROP_AUTO_MODE, oldValue, isAutoMode());
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        pcs.addPropertyChangeListener(listener);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        pcs.addPropertyChangeListener(propertyName, listener);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        pcs.removePropertyChangeListener(listener);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        pcs.removePropertyChangeListener(propertyName, listener);
    }

    /**
     * Fires the event to all available listeners.
     * @param propertyName The property name.
     * @param index The changed index.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue, boolean newValue) {
        pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    /**
     * Fires the event to all available listeners.
     * @param propertyName The property name.
     * @param index The changed index.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void fireIndexedPropertyChange(String propertyName, int index, int oldValue, int newValue) {
        pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    /**
     * Fires the event to all available listeners.
     * @param propertyName The property name.
     * @param index The changed index.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void fireIndexedPropertyChange(String propertyName, int index, Object oldValue, Object newValue) {
        pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
    }

    /**
     * Fires the event to all listeners.
     * @param evt The event to fire.
     */
    protected void firePropertyChange(PropertyChangeEvent evt) {
        pcs.firePropertyChange(evt);
    }

    /**
     * Fires the event to all listeners.
     * @param propertyName The changed property.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
        pcs.firePropertyChange(propertyName, oldValue, newValue);
    }

    /**
     * Fires the event to all listeners.
     * @param propertyName The changed property.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
        pcs.firePropertyChange(propertyName, oldValue, newValue);
    }

    /**
     * Fires the event to all listeners.
     * @param propertyName The changed property.
     * @param oldValue The old value.
     * @param newValue The new value.
     */
    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        pcs.firePropertyChange(propertyName, oldValue, newValue);
    }
}