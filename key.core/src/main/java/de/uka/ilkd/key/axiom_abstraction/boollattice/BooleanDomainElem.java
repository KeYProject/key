/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;

/**
 * A domain element of the simple boolean lattice.
 *
 * @author Dominic Scheurer
 */
public abstract class BooleanDomainElem extends AbstractDomainElement {

    /**
     * @return true iff this element is the bottom element.
     */
    public boolean isBottom() {
        return this instanceof Bottom;
    }

    /**
     * @return true iff this element is the false element.
     */
    public boolean isFalse() {
        return this instanceof False;
    }

    /**
     * @return true iff this element is the true element.
     */
    public boolean isTrue() {
        return this instanceof True;
    }

    /**
     * @return true iff this element is the top element.
     */
    public boolean isTop() {
        return this instanceof Top;
    }

}
