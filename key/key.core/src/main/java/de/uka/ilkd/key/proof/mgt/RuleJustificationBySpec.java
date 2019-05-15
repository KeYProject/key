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

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.Contract;


public class RuleJustificationBySpec implements RuleJustification {
    
    private final Contract spec;
    
    
    public RuleJustificationBySpec(Contract spec) {
        this.spec = spec;
    }
    
    
    /**
     * Contracts for stubs are considered axioms; other contracts not.
     */
    public boolean isAxiomJustification() {
        return spec.getTarget() instanceof IProgramMethod
               && !((IProgramMethod)spec.getTarget()).isModel()
               && ((IProgramMethod)spec.getTarget()).getBody() == null;
    }
    
    
    public Contract getSpec() {
        return spec;
    }
}