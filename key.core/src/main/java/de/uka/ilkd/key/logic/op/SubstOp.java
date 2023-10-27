/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableArray;

/**
 * Standard first-order substitution operator, resolving clashes but not preventing (usually
 * unsound) substitution of non-rigid terms across modal operators. Currently, only the subclass
 * <code>WarySubstOp</code> is used and accessible through the key parser.
 */
public abstract class SubstOp extends AbstractOperator {

    protected SubstOp(Name name) {
        super(name, 2, new Boolean[] { false, true }, true);
    }


    /**
     * @return sort of the second subterm or throws an IllegalArgumentException if the given term
     *         has no correct (2=) arity
     */
    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        if (terms.size() == 2) {
            return terms.get(1).sort();
        } else {
            throw new IllegalArgumentException(
                "Cannot determine sort of " + "invalid term (Wrong arity).");
        }
    }


    /**
     * @return true iff the sort of the subterm 0 of the given term has the same sort as or a
     *         subsort of the variable to be substituted and the term's arity is 2 and the numer of
     *         variables bound there is 0 for the 0th subterm and 1 for the 1st subterm.
     */
    @Override
    protected void additionalValidTopLevel(Term term) {
        if (term.varsBoundHere(1).size() != 1) {
            throw new TermCreationException(this, term);
        }
        Sort substSort = term.sub(0).sort();
        Sort varSort = term.varsBoundHere(1).get(0).sort();
        if (!substSort.extendsTrans(varSort)) {
            throw new TermCreationException(this, term);
        }
    }


    /**
     * Apply this substitution operator to <code>term</code>, which has this operator as top-level
     * operator
     *
     * @param term the {@link Term} on which to apply the substitution
     * @param tb the {@link TermBuilder} to use for term construction
     */
    public abstract Term apply(Term term, TermBuilder tb);// {
    // QuantifiableVariable v = term.varsBoundHere(1).getQuantifiableVariable(0);
    // ClashFreeSubst cfSubst = new ClashFreeSubst(v, term.sub(0));
    // Term res = cfSubst.apply(term.sub(1));
    // return res;
    // }
}
