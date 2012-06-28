package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
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
    public InitConfig load(File file, List<File> classPath, File bootClassPath) throws FileNotFoundException, ProofInputException {
       ProblemLoader loader = new ProblemLoader(file, classPath, bootClassPath, getMediator());
       EnvInput envInput = loader.createEnvInput(file, classPath, bootClassPath);
       ProblemInitializer init = createProblemInitializer();
       return init.prepare(envInput);
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
    public void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
       getMediator().setProof(proof);
       getMediator().startAutoMode(goals);
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
