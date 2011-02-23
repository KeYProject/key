// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init;


/** Reading prover input failed
 */
public class ProofInputException extends Exception {

    private final String message;

    public ProofInputException(Exception e) {
        super(e.getMessage());
        message = e.toString();
        initCause(e);
    }

    public ProofInputException(String message) {
        super(message);
        this.message = message;
    }

    public String toString() {
        return message;
    }
}
