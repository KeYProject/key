/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;


/**
 * This class defines the logic equality operator {@code =}. It is a binary predicate accepting
 * arbitrary terms (of sort "any") as arguments.
 *
 * It also defines the formula equivalence operator {@code <->} (which could alternatively be seen
 * as a Junctor).
 */
public final class Equality extends JAbstractSortedOperator {

    /**
     * the usual 'equality' operator '='
     */
    public static final Equality EQUALS = new Equality(new Name("equals"), JavaDLTheory.ANY);

    /**
     * the usual 'equivalence' operator {@code <->} (be {@code A, B} formulae then {@code A <-> B}
     * is true
     * if and only if {@code A} and {@code B} have the same truth value
     */
    public static final Equality EQV = new Equality(new Name("equiv"), JavaDLTheory.FORMULA);


    private Equality(Name name, Sort targetSort) {
        super(name, new Sort[] { targetSort, targetSort }, JavaDLTheory.FORMULA, true);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(name() + " has no children");
    }
}
