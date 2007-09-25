// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//



package de.uka.ilkd.key.counterexample;

import de.uka.ilkd.key.logic.CExProblem;

/**
 * An instance of this class contains the fully generated calculus including all components generated througout the inherited classes: static clauses, sort dependent clauses, clauses generated from axioms and the clause representing the conjecture.
 * @author Sonja Pieper
 * @version 0.1
 * @see Calculus 
 */
public class ConjCalculus extends AxiomCalculus {

    CExProblem problem;
    Clauses conjecture;

	public ConjCalculus(CExProblem cep){
	    super(cep.getAdt());
	    problem = cep;
	    
	    conjecture = new Clauses(); //@@@
	    this.all.add(conjecture);
	}

    public Clauses getConjectureClause(){
        return conjecture;
    }
}
