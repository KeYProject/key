// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * @deprecated
 */
public interface Contract {

    void addCompoundProof(ProofAggregate pl);

    void removeCompoundProof(ProofAggregate pl);

    List getProofs();

    Object getObjectOfContract();

    void setProofEnv(ProofEnvironment env);

    ProofEnvironment getProofEnv();

    ProofOblInput getProofOblInput(Proof proof);
   
    /** Sets the textual header needed to later load the proof of this contract.
     *  This header is usually copied from the problem, in which the contract
     *  is defined/used.
     */
    void setHeader(String s);

    String getName();    

}
