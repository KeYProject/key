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

import de.uka.ilkd.key.proof.ProofAggregate;


/**
 * Represents something that produces an input proof obligation for the 
 * prover. A .key file or a proof obligation generated from a CASE tool may 
 * be instances. During reading the input the
 * given initial configuration may become modified. The modification
 * can be controlled by a modification strategy.
 */
public interface ProofOblInput {
    
    /** 
     * Returns the name of the proof obligation input.
     */
    String name();
    
    boolean askUserForEnvironment();
    
    void readActivatedChoices() throws ProofInputException;

    void readProblem(ModStrategy mod) throws ProofInputException;

    /** 
     * Returns the proof obligation term as result of the proof obligation
     * input. If there is still no input available because nothing has
     * been read yet null is returned.
     */
    ProofAggregate getPO() throws ProofInputException;
    
    /**
     * If true, then this PO implies the passed one.
     */
    boolean implies(ProofOblInput po);
 }
