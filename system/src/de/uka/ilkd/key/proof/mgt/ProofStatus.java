// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;


public enum ProofStatus {
    OPEN, 
    CLOSED_BUT_LEMMAS_LEFT, 
    CLOSED;

    public boolean getProofClosed() {
	return this == CLOSED;
    }
    
    public boolean getProofClosedButLemmasLeft() {
	return this == CLOSED_BUT_LEMMAS_LEFT;
    }
    
    public boolean getProofOpen() {
	return this == OPEN;
    }
    
    public ProofStatus combine(ProofStatus ps) {
        if(getProofOpen() || ps.getProofOpen()) {
            return OPEN;
        } else if(getProofClosedButLemmasLeft() || ps.getProofClosedButLemmasLeft()) { 
            return CLOSED_BUT_LEMMAS_LEFT;
        } else {
            return CLOSED;
        }
    }
}