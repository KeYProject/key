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

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;


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
     * Reads the libraries settings.
     */
    LibrariesSettings readLibrariesSettings() throws ProofInputException;
    
    /** 
     * Reads the Java path.
     */
    String readJavaPath() throws ProofInputException;
    
    /** 
     * gets the classpath elements to be considered here.
     */
    List<File> readClassPath() throws ProofInputException;
    
    /** 
     * Reads the input using the given modification strategy, i.e.,
     * parts of the input do not modify the initial configuration while
     * others do.
     */
    void read(ModStrategy mod) throws ProofInputException;
}
