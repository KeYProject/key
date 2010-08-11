// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Quantifier;

/**
 * Axiom inherits from Term. It represents an axiom in an abstract
 * data type. It consists of a conjunction of equalities and
 * inequalities, which are implicitly quantified.
 */

public class Axiom { //@@@ this class is not yet designed
    
    private Term term;
    
    public Axiom(Term t){
	if (t.op() instanceof Quantifier) { 
	    term = t; 
	} else { 
	    throw new IllegalArgumentException("Axioms require quantified terms"); 
	}
    }

    
    public Term getAxiomTerm() {
	return term;
    }
    
}

