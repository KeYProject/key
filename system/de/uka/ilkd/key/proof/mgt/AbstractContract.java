// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.ProofAggregate;

/**
 * @deprecated
 */
public abstract class AbstractContract implements Contract {

    protected List proofs = new LinkedList();
    protected ProofEnvironment env;
    protected String header;

    public void setProofEnv(ProofEnvironment env) {
	if (this.env==null) {
	    this.env=env;
	} else if (this.env!=env) {
	    throw new IllegalStateException("Contract may belong to "
					    +"only one environment.");
	}
    }

    public ProofEnvironment getProofEnv() {
	return env;
    }
    public List getProofs() {
	return proofs;
    }

    public void addCompoundProof(ProofAggregate pl) {
	proofs.add(pl);
    }

    public void removeCompoundProof(ProofAggregate pl) {
	proofs.remove(pl);
    }

    /** Sets the textual header needed to later load the proof of this contract.
     *  This header is usually copied from the problem, in which the contract
     *  is defined/used.
     */
    public void setHeader(String s) {
        if (header==null) header = s;
    }


}
