/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.boollattice;

import java.util.Iterator;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;

/**
 * A simple lattice for booleans.
 *
 * @author Dominic Scheurer
 */
public class BooleanLattice extends AbstractDomainLattice {

    /**
     * All elements of this abstract domain.
     */
    public static final AbstractDomainElement[] ABSTRACT_DOMAIN_ELEMS =
        { Bottom.getInstance(), False.getInstance(), True.getInstance(), Top.getInstance() };

    /**
     * The singleton instance of the lattice.
     */
    private static final BooleanLattice INSTANCE = new BooleanLattice();

    /**
     * Private constructor: Singleton.
     */
    private BooleanLattice() {
    }

    /**
     * @return The singleton instance of this lattice.
     */
    public static BooleanLattice getInstance() {
        return INSTANCE;
    }

    @Override
    public AbstractDomainElement join(AbstractDomainElement elem1, AbstractDomainElement elem2) {

        if (!(elem1 instanceof BooleanDomainElem a) || !(elem2 instanceof BooleanDomainElem b)) {
            throw new IllegalArgumentException(
                "Expected arguments of the abstract domain of sign analysis.");
        }

        if (a.isTop() || b.isTop()) {
            return Top.getInstance();
        }

        if (a.isTrue()) {
            if (b.isFalse()) {
                return Top.getInstance();
            } else {
                return True.getInstance();
            }
        }

        if (a.isFalse()) {
            if (b.isTrue()) {
                return Top.getInstance();
            } else {
                return False.getInstance();
            }
        }

        assert (a.isBottom()) : "Bug in boolean lattice implementation.";
        return b;
    }

    @Override
    public Iterator<AbstractDomainElement> iterator() {
        return new Iterator<>() {

            int pos = 0;
            final int size = ABSTRACT_DOMAIN_ELEMS.length;

            @Override
            public boolean hasNext() {
                return pos < size - 1;
            }

            @Override
            public AbstractDomainElement next() {
                return ABSTRACT_DOMAIN_ELEMS[pos++];
            }

            @Override
            public void remove() {
            }
        };
    }

}
