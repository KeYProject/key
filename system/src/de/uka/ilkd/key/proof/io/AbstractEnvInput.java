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


package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;



/**
 * A simple EnvInput which includes default rules and a Java path.
 */
public abstract class AbstractEnvInput implements EnvInput {

    protected final String name;
    protected final String javaPath;    
    protected final List<File> classPath;
    protected final File bootClassPath;
    protected final Includes includes;    
    protected final Profile profile;
    
    protected InitConfig initConfig;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public AbstractEnvInput(String name,
	    		    String javaPath,
	    		    List<File> classPath,
	    		    File bootClassPath,
	    		    Profile profile) {
   assert profile != null;
	this.name     = name;
	this.javaPath = javaPath;
	this.classPath = classPath;
	this.bootClassPath = bootClassPath;
	this.includes = new Includes();
	this.profile = profile;
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


    @Override
    public final List<File> readClassPath() throws ProofInputException {
        return classPath;
    }
    

    @Override
    public File readBootClassPath() {
        return bootClassPath;
    }
    
    @Override
    public Profile getProfile() {
        return profile;
    }
}
