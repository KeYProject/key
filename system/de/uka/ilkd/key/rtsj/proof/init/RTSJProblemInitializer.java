// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.proof.init;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.EnvInput;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rtsj.java.RTSJInfo;

public class RTSJProblemInitializer extends ProblemInitializer {

    public RTSJProblemInitializer(IMain main) {
	super(main);	
    }
    
    protected void readEnvInput(EnvInput envInput,
	      InitConfig initConfig)
	throws ProofInputException {
	super.readEnvInput(envInput, initConfig);
	Namespace progVars = initConfig.namespaces().programVariables();
	ProgramVariable defMem = ((RTSJInfo) initConfig.getServices().getJavaInfo()).getDefaultMemoryArea();
	ProgramVariable immortalMem = ((RTSJInfo) initConfig.getServices().getJavaInfo()).getImmortalMemoryArea();            
	if (progVars.lookup(defMem.name()) == null) {
	    progVars.add(defMem);
	}
	if (progVars.lookup(immortalMem.name()) == null) {
	    progVars.add(immortalMem);
	}
    }

}
