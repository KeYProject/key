// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.List;
import java.io.File;



/** 
 * A simple EnvInput which includes default rules and a Java path.
 */
public abstract class AbstractEnvInput implements EnvInput {
    
    private final String name;
    private final String javaPath;
    protected InitConfig initConfig;
    
    private Includes includes;
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public AbstractEnvInput(String name, 
	    		    String javaPath) {
	this.name     = name;
	this.javaPath = javaPath;
	this.includes = new Includes();
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public final String name() {
	return name;
    }
    

    @Override
    public final int getNumberOfChars() {
	return 1;
    }
        
    
    @Override
    public final void setInitConfig(InitConfig initConfig) {
	this.initConfig = initConfig;
    }
    
    
    @Override
    public final Includes readIncludes() throws ProofInputException {
	assert initConfig != null;
	return includes;
    }
    
    
    @Override
    public final String readJavaPath() throws ProofInputException {
	return javaPath;
    }
    
    // no class path elements here
    @Override
    public final List<File> readClassPath() throws ProofInputException {
        return null;
    }
    
}
