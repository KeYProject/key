package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.rule.*;

public abstract class AbstractUserInterface implements UserInterface {

	public void loadProblem(File file, List<File> classPath,
	        File bootClassPath, KeYMediator mediator) {
		final ProblemLoader pl = new ProblemLoader(file, classPath,
		        bootClassPath, mediator);
		pl.addTaskListener(this);
		pl.run();
	}

	@Override
	public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, Services services) {
		if (app instanceof IBuiltInRuleApp) {
			app = ((IBuiltInRuleApp)app).tryToInstantiate(goal);
		}
		// cannot complete that app
		return app.complete() ? app : null;
	}

}
