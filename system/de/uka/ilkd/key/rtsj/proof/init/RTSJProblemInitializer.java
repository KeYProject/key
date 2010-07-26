package de.uka.ilkd.key.rtsj.proof.init;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.EnvInput;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;

public class RTSJProblemInitializer extends ProblemInitializer {

    public RTSJProblemInitializer(IMain main) {
	super(main);	
    }
    
    protected void readEnvInput(EnvInput envInput,
	      InitConfig initConfig)
	throws ProofInputException {
	super.readEnvInput(envInput, initConfig);
	Namespace progVars = initConfig.namespaces().programVariables();
	ProgramVariable defMem = initConfig.getServices().getJavaInfo().getDefaultMemoryArea();
	ProgramVariable immortalMem = initConfig.getServices().getJavaInfo().getImmortalMemoryArea();            
	if (progVars.lookup(defMem.name()) == null) {
	    progVars.add(defMem);
	}
	if (progVars.lookup(immortalMem.name()) == null) {
	    progVars.add(immortalMem);
	}
    }

}
