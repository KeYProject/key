/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * The bound uniqueness checker ensures that schemavariables can be bound at most once in the
 * <tt>\find</tt> and <tt>\assumes</tt> part of a taclet. The justification for this restriction is
 * to prevent the user to write taclets that match only in very rare cases, e.g. <code>
 *   \assumes (==>\forall var; phi)
 *   \find (\forall var; phi ==>)
 * </code> would nearly never match, as <tt>var</tt> would be required to match the same object.
 */
public class BoundUniquenessChecker {

    private final HashSet<QuantifiableVariable> boundVars =
        new LinkedHashSet<>();
    private ImmutableList<JTerm> terms = ImmutableSLList.nil();

    public BoundUniquenessChecker(Sequent seq) {
        addAll(seq);
    }

    public BoundUniquenessChecker(JTerm t, Sequent seq) {
        addTerm(t);
        addAll(seq);
    }

    public BoundUniquenessChecker(SyntaxElement find, Sequent seq) {
        if (find instanceof JTerm t)
            addTerm(t);
        else if (find instanceof Sequent s)
            addAll(s);
        addAll(seq);
    }

    /**
     * adds <tt>term</tt> to the list of terms to include in the uniqueness check
     *
     * @param term a Term
     */
    public void addTerm(JTerm term) {
        terms = terms.prepend(term);
    }

    /**
     * adds all formulas in the sequent to the list of terms to include in the uniqueness check
     *
     * @param seq the Sequent with the formulas to add
     */
    public void addAll(Sequent seq) {
        for (final SequentFormula cf : seq) {
            terms = terms.prepend((JTerm) cf.formula());
        }
    }

    // recursive helper
    private boolean correct(JTerm t) {
        /*
         * Note that a term can bound a variable in several subterms.
         */
        final HashSet<QuantifiableVariable> localVars = new LinkedHashSet<>(10);

        for (int i = 0, ar = t.arity(); i < ar; i++) {
            for (int j = 0, sz = t.varsBoundHere(i).size(); j < sz; j++) {
                final QuantifiableVariable qv = t.varsBoundHere(i).get(j);
                if (boundVars.contains(qv)) {
                    return false;
                } else {
                    localVars.add(qv);
                }
            }
        }

        boundVars.addAll(localVars);

        for (int i = 0, ar = t.arity(); i < ar; ++i) {
            if (!correct(t.sub(i))) {
                return false;
            }
        }
        return true;
    }


    /**
     * returns true if any variable is bound at most once in the given set of terms
     */
    public boolean correct() {
        for (final JTerm term : terms) {
            if (!correct(term)) {
                return false;
            }
        }
        return true;
    }

}
