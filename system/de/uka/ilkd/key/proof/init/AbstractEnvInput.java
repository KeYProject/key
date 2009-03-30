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
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;



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

    public String name() {
	return name;
    }
    

    public int getNumberOfChars() {
	return 1;
    }
        
    
    public void setInitConfig(InitConfig initConfig) {
	this.initConfig = initConfig;
    }
    
    
    public Includes readIncludes() throws ProofInputException {
	assert initConfig != null;
	return includes;
    }
    
    
    public LibrariesSettings readLibrariesSettings() 
    		throws ProofInputException {
	return ProofSettings.DEFAULT_SETTINGS.getLibrariesSettings();
    }
    
    
    public String readJavaPath() throws ProofInputException {
	return javaPath;
    }
    
    // no class path elements here
    public List<File> readClassPath() throws ProofInputException {
        return null;
    }
    
}
