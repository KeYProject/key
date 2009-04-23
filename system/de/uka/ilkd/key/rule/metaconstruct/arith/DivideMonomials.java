// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct.arith;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Metaoperator for computing the result of dividing one monomial by another
 */
public class DivideMonomials extends AbstractMetaOperator {

    public DivideMonomials() {
        super ( new Name ( "#divideMonomials" ), 2 );
    }
    
    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return term.op() instanceof DivideMonomials && term.arity()==arity();
    }
    
    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        final Term arg1 = term.sub ( 0 );
        final Term arg2 = term.sub ( 1 );

        final Monomial m1 = Monomial.create ( arg1, services );
        final Monomial m2 = Monomial.create ( arg2, services );

        final Monomial res = m2.reduce ( m1 );
        return res.toTerm ( services );
    }

}
