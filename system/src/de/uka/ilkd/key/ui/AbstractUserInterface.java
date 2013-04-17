// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public abstract class AbstractUserInterface implements UserInterface {

	public void loadProblem(File file, List<File> classPath,
	        File bootClassPath, KeYMediator mediator) {
		final ProblemLoader pl = new ProblemLoader(file, classPath,
		        bootClassPath, mediator);
		pl.addTaskListener(this);
		pl.run();
	}

    @Override
	public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
		if (app instanceof IBuiltInRuleApp) {
			app = ((IBuiltInRuleApp)app).tryToInstantiate(goal);
		}
		// cannot complete that app
		return app.complete() ? app : null;
	}

    /**
     * {@inheritDoc}
     */
    @Override
    public DefaultProblemLoader load(File file, List<File> classPath, File bootClassPath) throws ProblemLoaderException {
       try {
          getMediator().stopInterface(true);
          DefaultProblemLoader loader = new DefaultProblemLoader(file, classPath, bootClassPath, getMediator());
          loader.load();
          return loader;
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
       ProblemInitializer init = createProblemInitializer();
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
}