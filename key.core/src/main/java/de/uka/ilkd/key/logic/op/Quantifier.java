/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;

/**
 * The two objects of this class represent the universal and the existential quantifier,
 * respectively.
 */
public final class Quantifier extends JAbstractSortedOperator {
    public static final Name ALL_NAME = new Name("all");
    public static final Name EX_NAME = new Name("exists");

    /**
     * the usual {@code forall} operator 'all' (be A a formula then {@code forall x.A} is true if
     * and only if for
     * all elements d of the universe {@code A{x<-d}} (x substituted with d) is true
     */
    public static final Quantifier ALL = new Quantifier(ALL_NAME);

    /**
     * the usual {@code exists}-operator (be {@code A} a formula then {@code exists x; A} is true if
     * and only if there
     * is at least one element d of the universe such that {@code A{x<-d}} (x substituted with d) is
     * true
     */
    public static final Quantifier EX = new Quantifier(EX_NAME);


    private Quantifier(Name name) {
        super(name, new Sort[] { JavaDLTheory.FORMULA }, JavaDLTheory.FORMULA,
            new Boolean[] { true }, true);
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
