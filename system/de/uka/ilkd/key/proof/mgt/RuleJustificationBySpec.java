// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;


public class RuleJustificationBySpec implements RuleJustification {
    
    private final ContractWithInvs spec;
    
    
    public RuleJustificationBySpec(ContractWithInvs spec) {
        this.spec = spec;
    }
    
    
    public boolean isAxiomJustification() {
	//contracts for stubs are considered axioms
	//XXX: The observed state semantics allows choosing any set of invariants
	//when applying the contract. But not all may be preserved by a method
	//present only as a stub!
        return spec.contract.getProgramMethod().getBody() == null;
    }
    
    
    public ContractWithInvs getSpec() {
        return spec;
    }
}
