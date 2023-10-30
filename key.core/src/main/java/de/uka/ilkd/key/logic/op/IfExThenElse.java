/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableArray;


/**
 * This singleton class implements a conditional operator "\ifEx iv; (phi) \then (t1) \else (t2)",
 * where iv is an integer logic variable, phi is a formula, and where t1 and t2 are terms with the
 * same sort. The variable iv is bound in phi and in t1, but not in t2.
 */
public final class IfExThenElse extends AbstractOperator {

    public static final IfExThenElse IF_EX_THEN_ELSE = new IfExThenElse();


    private IfExThenElse() {
        super(new Name("ifExThenElse"), 3, new Boolean[] { true, true, false }, true);
    }


    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        return terms.get(1).sort();
    }


    @Override
    protected void additionalValidTopLevel(Term term) {
        for (QuantifiableVariable var : term.varsBoundHere(0)) {
            if (!var.sort().name().toString().equals("int")) {
                throw new TermCreationException(this, term);
            }
        }

        final Sort s0 = term.sub(0).sort();
        final Sort s1 = term.sub(1).sort();
        final Sort s2 = term.sub(2).sort();

        if (!(s0 == Sort.FORMULA && s1.equals(s2))) {
            throw new TermCreationException(this, term);
        }
    }
}
