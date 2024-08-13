/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.AbstractOperator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.TermBuilder;

/**
 * Standard first-order substitution operator, resolving clashes but not preventing (usually
 * unsound) substitution of non-rigid terms across modal operators. Currently, only the subclass
 * <code>WarySubstOp</code> is used and accessible through the key parser.
 */
public class SubstOp extends AbstractOperator {
    /**
     * the wary substitution operator {@code {var<-term}'}. {@code {x<-d}'A(x)} means replace all
     * free occurrences
     * of variable x in A with d, however without replacing x with a non-rigid A below modalities
     */
    public static final SubstOp SUBST = new SubstOp(new Name("subst"));

    protected SubstOp(Name name) {
        super(name, 2, new Boolean[] { false, true }, true);
    }

    /**
     * @return sort of the second subterm or throws an IllegalArgumentException if the given term
     *         has no correct (2=) arity
     */
    @Override
    public Sort sort(Sort[] sorts) {
        if (sorts.length == 2) {
            return sorts[1];
        } else {
            throw new IllegalArgumentException(
                "Cannot determine sort of " + "invalid term (Wrong arity).");
        }
    }

    @Override
    public <T extends Term> void validTopLevelException(T term) throws TermCreationException {
        super.validTopLevelException(term);
        if (term.varsBoundHere(1).size() != 1) {
            throw new TermCreationException(this, term);
        }
        Sort substSort = term.sub(0).sort();
        Sort varSort = term.varsBoundHere(1).get(0).sort();
        if (!substSort.extendsTrans(varSort)) {
            throw new TermCreationException(this, term);
        }
    }

    public Term apply(Term term, TermBuilder tb) {
        QuantifiableVariable v = term.varsBoundHere(1).get(0);
        // WaryClashFreeSubst cfSubst = new WaryClashFreeSubst(v, term.sub(0), tb);
        // return cfSubst.apply(term.sub(1));
        // TODO
        return term;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("SubstOp " + name() + " has no children");
    }
}
