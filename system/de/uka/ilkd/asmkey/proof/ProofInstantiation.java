// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;


/** Class represents an instantiation of a variable.
 * @see ProofRule
 *
 * @author Hubert Schmid */

public final class ProofInstantiation {

    /** name of variable */
    private final String variable;

    /** string representation of term */
    private final String term;


    ProofInstantiation(String variable, String term) {
        this.variable = variable;
        this.term = term;
    }


    /** Return name of variable. */
    public String getVariable() {
        return variable;
    }

    /** Return the string representation of the term. The term is not
     * parsed. */
    public String getTerm() {
        return term;
    }

}
