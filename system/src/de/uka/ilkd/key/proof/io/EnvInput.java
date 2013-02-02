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
import de.uka.ilkd.key.proof.init.ProofInputException;


/** 
 * Represents an entity read to produce an environment to read a proof
 * obligation. Environment means the initial configuration of a prover
 * containing namespaces and Java model.
 */
public interface EnvInput {

    /**
     * Returns the name of this input.
     */
    String name();

    /**
     * Returns the total numbers of chars that can be read in this input.
     */
    int getNumberOfChars();

    /**
     * Sets the initial configuration the read environment input should be
     * added to. Must be called before calling any of the read* methods.
     */
    void setInitConfig(InitConfig initConfig);

    /**
     * Reads the include section and returns an Includes object.
     */
    Includes readIncludes() throws ProofInputException;
    
    /** 
     * Reads the Java path.
     */
    String readJavaPath() throws ProofInputException;

    /**
     * gets the classpath elements to be considered here.
     */
    List<File> readClassPath() throws ProofInputException;

    /**
     * gets the boot classpath element, null if none set.
     */
    File readBootClassPath();
    
    /**
     * Reads the input using the given modification strategy, i.e.,
     * parts of the input do not modify the initial configuration while
     * others do.
     */
    void read() throws ProofInputException;
}
