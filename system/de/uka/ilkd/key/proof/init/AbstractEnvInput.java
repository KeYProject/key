// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;



/** 
 * A simple EnvInput which includes default rules and a Java path.
 */
public abstract class AbstractEnvInput implements EnvInput {
    
    private final String name;
    private final String javaPath;
    protected InitConfig initConfig;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public AbstractEnvInput(String name, 
	    		    String javaPath) {
	this.name     = name;
	this.javaPath = javaPath;
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
	return new Includes();
    }
    
    
    public LibrariesSettings readLibrariesSettings() 
    		throws ProofInputException {
	return ProofSettings.DEFAULT_SETTINGS.getLibrariesSettings();
    }
    
    
    public String readJavaPath() throws ProofInputException {
	return javaPath;
    }
    
    // no class path elements here
    public ListOfString readClassPath() throws ProofInputException {
        return null;
    }
    
}
