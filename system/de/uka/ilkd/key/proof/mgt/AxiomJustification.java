// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;


public class AxiomJustification implements RuleJustification {

    public static final AxiomJustification INSTANCE = new AxiomJustification();
    
    private AxiomJustification() {
    }

    public String toString() {
	return "axiom justification";
    }

    public boolean isAxiomJustification() {
	return true;
    }    
}
