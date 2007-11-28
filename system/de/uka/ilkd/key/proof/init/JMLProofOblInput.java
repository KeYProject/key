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

public interface JMLProofOblInput extends ProofOblInput {

    /**
     * Checks if the methods used in the specification that underlies this
     * JMLProofOblInput are declared with the modifier pure.
     */
    boolean checkPurity();

    /**
     * Creates program variables section for the problem header.
     */
    String createProgramVarsSection();

    /**
     * Creates java section for the problem header.
     */
    String createJavaSection();

    /**
     * Creates the problem header.
     */
    String createProblemHeader();
}


