// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;


/**
 * Represents something that produces an input proof obligation for the 
 * prover. A .key file or a proof obligation generated from a CASE tool may 
 * be instances. An instance can be called to set an initial configuration,
 * that is modified during reading the input (using <code>setInitConfig</code>), 
 * to get the read proof 
 * obligation (using <code>getProblemTerm</code>). During reading the input
 * given initial configuration may become modified. The modification
 * can be controlled by a modification strategy.
 */
public interface ProofOblInput {
    
    /** returns the name of the proof obligation input.
     */
    String name();
    
    boolean askUserForEnvironment();
    
    /** Set the initial configuration used to read the input. It may become
     * modified during reading depending on the modification strategy used
     * for reading. Must be called before calling any of the read* methods.
     */
    void setInitConfig(InitConfig i);
    
    void readActivatedChoices() throws ProofInputException;
    
    void readSpecs();

    void readProblem(ModStrategy mod) throws ProofInputException;

    /** returns the proof obligation term as result of the proof obligation
     * input. If there is still no input available because nothing has
     * been read yet null is returned.
     */
    ProofAggregate getPO();
    
    Contractable[] getObjectOfContract();
    
    boolean initContract(Contract ct);
 }
