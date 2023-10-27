/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The two objects of this class represent the universal and the existential quantifier,
 * respectively.
 */
public final class Quantifier extends AbstractSortedOperator {
    public static final Name ALL_NAME = new Name("all");
    public static final Name EX_NAME = new Name("exists");

    /**
     * the usual 'forall' operator 'all' (be A a formula then 'all x.A' is true if and only if for
     * all elements d of the universe A{x<-d} (x substituted with d) is true
     */
    public static final Quantifier ALL = new Quantifier(ALL_NAME);

    /**
     * the usual 'exists' operator 'ex' (be A a formula then 'ex x.A' is true if and only if there
     * is at least one elements d of the universe such that A{x<-d} (x substituted with d) is true
     */
    public static final Quantifier EX = new Quantifier(EX_NAME);


    private Quantifier(Name name) {
        super(name, new Sort[] { Sort.FORMULA }, Sort.FORMULA, new Boolean[] { true }, true);
    }
}
