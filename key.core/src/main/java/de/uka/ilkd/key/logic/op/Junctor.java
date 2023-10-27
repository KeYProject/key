/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Class of junctor operators, i.e., operators connecting a given number of formula to create
 * another formula. There are six such operators: true, false, conjunction, disjunction, negation,
 * and implication.
 */
public final class Junctor extends AbstractSortedOperator {

    /**
     * the true constant
     */
    public static final Junctor TRUE = new Junctor(new Name("true"), 0);

    /**
     * the false constant
     */
    public static final Junctor FALSE = new Junctor(new Name("false"), 0);

    /**
     * the usual 'and' operator '/\' (be A, B formulae then 'A /\ B' is true if and only if A is
     * true and B is true
     */
    public static final Junctor AND = new Junctor(new Name("and"), 2);

    /**
     * the usual 'or' operator '\/' (be A, B formulae then 'A \/ B' is true if and only if A is true
     * or B is true
     */
    public static final Junctor OR = new Junctor(new Name("or"), 2);

    /**
     * the usual 'negation' operator '-'
     */
    public static final Junctor NOT = new Junctor(new Name("not"), 1);

    /**
     * the usual 'implication' operator '->' (be A, B formulae then 'A -> B' is true if and only if
     * A is false or B is true
     */
    public static final Junctor IMP = new Junctor(new Name("imp"), 2);


    private static Sort[] createFormulaSortArray(int arity) {
        Sort[] result = new Sort[arity];
        for (int i = 0; i < arity; i++) {
            result[i] = Sort.FORMULA;
        }
        return result;
    }


    private Junctor(Name name, int arity) {
        super(name, createFormulaSortArray(arity), Sort.FORMULA, true);
    }
}
