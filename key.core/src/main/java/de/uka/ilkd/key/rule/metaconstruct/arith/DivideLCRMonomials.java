/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;

/**
 * Metaoperator for computing the result of dividing one monomial by another
 */
public final class DivideLCRMonomials extends AbstractTermTransformer {

    public DivideLCRMonomials() {
        super(new Name("#divideLCRMonomials"), 2);
    }


    /** calculates the resulting term. */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final Term arg1 = term.sub(0);
        final Term arg2 = term.sub(1);

        final Monomial m1 = Monomial.create(arg1, services);
        final Monomial m2 = Monomial.create(arg2, services);

        final Monomial res = m2.divideLCR(m1);
        return res.toTerm(services);
    }

}
