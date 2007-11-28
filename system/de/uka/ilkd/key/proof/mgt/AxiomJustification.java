// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;

public class AxiomJustification implements RuleJustification {

    public static final AxiomJustification INSTANCE = new AxiomJustification();
    private List emptyList = new LinkedList();

    public String toString() {
	return "axiom justification";
    }

    public DepAnalysis dependsOn(Proof p) {
	return DepAnalysis.getInstance(false, null, p);
    }

    public boolean isAxiomJustification() {
	return true;
    }
    
    public List getProofList() {
	return emptyList;
    }

}
