package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.ProblemLoader;

public abstract class AbstractUserInterface implements UserInterface {            
    
	public void loadProblem(File file, List<File> classPath, File bootClassPath, KeYMediator mediator) {
        final ProblemLoader pl = 
            new ProblemLoader(file, classPath, bootClassPath, mediator);
        pl.addTaskListener(this);
        pl.run();
    }

}
