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

// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.proof.mgt.ProofStatus;

public class SingleProof extends ProofAggregate {

    private final Proof proof;
    
    public SingleProof(Proof p, String name) {
        super(name);
        assert p != null;
        this.proof = p;
    }
    
    @Override
    public ProofStatus getStatus() {
        return proof.mgt().getStatus();
    }
    
    @Override
    public Proof[] getProofs() {
        return new Proof[]{proof};
    }

    @Override
    public boolean equals(Object o) {
       if (!super.equals(o)) {
          return false;
       }
       final SingleProof other = (SingleProof) o;
       
       return proof == other.proof;       
    }
    
    
    @Override
    public int hashCode() {
       return super.hashCode() + proof.hashCode();
    }
    
    @Override    
    public int size() {
        return 1;
    }
    
    @Override    
    public ProofAggregate[] getChildren() {
        return new ProofAggregate[0];
    }
}