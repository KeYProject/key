// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.mgt;


import de.uka.ilkd.key.util.Debug;

public class ProofStatus {
    
    public final static ProofStatus OPEN = new ProofStatus(false, false, true);
    public final static ProofStatus CLOSED_BUT_LEMMAS_LEFT = new ProofStatus(false, true, false);
    public final static ProofStatus CLOSED = new ProofStatus(true, false, false);
    
    private boolean closed;
    private boolean closedButLemmasLeft;
    private boolean open;
    
    public ProofStatus(boolean closed, boolean closedButLemmasLeft, boolean open) {
	this.closed = closed;
	this.closedButLemmasLeft = closedButLemmasLeft;
	this.open = open;
    }
    
    public boolean getProofClosed() {
	return closed;
    }
    
    public boolean getProofClosedButLemmasLeft() {
	return closedButLemmasLeft;
    }
    
    public boolean getProofOpen() {
	return open;
    }
    
    public ProofStatus combineProofStatus(ProofStatus ps) {
        if (getProofOpen() || ps.getProofOpen()) return OPEN;
        if (getProofClosedButLemmasLeft() || ps.getProofClosedButLemmasLeft()) 
            return CLOSED_BUT_LEMMAS_LEFT;
        if (getProofClosed() || ps.getProofClosed()) return CLOSED;
        Debug.fail();
        return null;
    }
    
    public String toString() {
	if (closed && !closedButLemmasLeft && !open) {
	    return "This proof is really closed.";
	}
	if (!closed && closedButLemmasLeft && !open) {
	    return "This proof is closed but there are Lemmas left to be proven.";
	}
	if (!closed && !closedButLemmasLeft && open) {
	    return "This proof is still open!";
	}

	return "Illegal status!";
    }    
}
