/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.Objects;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.collection.ImmutableArray;


/**
 * All symbols acting as members of a term e.g. logical operators, predicates, functions, variables
 * etc. have to implement this interface.
 */
public interface Operator extends Named, SVSubstitute, EqualsModProofIrrelevancy {

    /**
     * the arity of this operator
     */
    int arity();


    /**
     * Determines the sort of the {@link Term} if it would be created using this Operator as top
     * level operator and the given terms as sub terms. The assumption that the constructed term
     * would be allowed is not checked.
     *
     * @param terms an array of Term containing the subterms of a (potential) term with this
     *        operator as top level operator
     * @return sort of the term with this operator as top level operator of the given substerms
     */
    Sort sort(ImmutableArray<Term> terms);


    /**
     * Tells whether the operator binds variables at the n-th subterm.
     */
    boolean bindVarsAt(int n);


    /**
     * Tells whether the operator is rigid.
     */
    boolean isRigid();


    /**
     * Checks whether the top level structure of the given @link Term is syntactically valid, given
     * the assumption that the top level operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal is NOT checked.
     *
     * @throws TermCreationException if a construction error was recognise
     */
    void validTopLevelException(Term term) throws TermCreationException;


    /**
     * @return true iff the top level structure of the {@link Term} is valid, i.e. its parameters
     *         and types are correct.
     */
    default boolean validTopLevel(Term term) {
        try {
            validTopLevelException(term);
            return true;
        } catch (TermCreationException e) {
            return false;
        }
    }

    @Override
    default boolean equalsModProofIrrelevancy(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof Operator)) {
            return false;
        }
        Operator that = (Operator) obj;
        // assume name and arity uniquely identifies operator
        return arity() == that.arity() && name().equals(that.name());
    }

    @Override
    default int hashCodeModProofIrrelevancy() {
        return Objects.hash(arity(), name());
    }
}
