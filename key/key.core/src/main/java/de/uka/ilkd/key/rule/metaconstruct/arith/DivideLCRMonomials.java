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

package de.uka.ilkd.key.rule.metaconstruct.arith;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
* Metaoperator for computing the result of dividing one monomial by another
*/
public final class DivideLCRMonomials extends AbstractTermTransformer {

    public DivideLCRMonomials() {
        super ( new Name ( "#divideLCRMonomials" ), 2 );
    }


    /** calculates the resulting term. */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term arg1 = term.sub ( 0 );
        final Term arg2 = term.sub ( 1 );

        final Monomial m1 = Monomial.create ( arg1, services );
        final Monomial m2 = Monomial.create ( arg2, services );

        final Monomial res = m2.divideLCR ( m1 );
        return res.toTerm ( services );
    }

}