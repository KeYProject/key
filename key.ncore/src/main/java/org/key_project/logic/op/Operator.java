/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Named;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

public interface Operator extends Named {
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

    abstract class Modality implements Operator {

    }
}
