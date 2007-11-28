// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.casetool.together;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.DefaultEnvInput;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;



/** 
 * EnvInput for Together.
 */
public class TogetherEnvInput extends DefaultEnvInput {
    
    private final TogetherModelClass modelClass;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public TogetherEnvInput(TogetherModelClass modelClass) {
	super("Together input", modelClass.getRootDirectory());
	this.modelClass = modelClass;
    }
    
           
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 

    public void read(ModStrategy mod) throws ProofInputException {
	if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
	
	//create UML info
	Services services = initConfig.getServices();
	services.setUMLInfo(modelClass.createUMLInfo(services));
    }
}
