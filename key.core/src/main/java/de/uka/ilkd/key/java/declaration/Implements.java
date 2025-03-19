/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Implements.
 *
 */

public class Implements extends InheritanceSpecification {

    /**
     * Implements.
     */

    public Implements() {}

    /**
     * Implements.
     *
     * @param supertype a type reference.
     */

    public Implements(TypeReference supertype) {
        super(supertype);
    }

    /**
     * Implements.
     *
     * @param typeRefs a type reference array.
     */

    public Implements(TypeReference[] typeRefs) {
        super(typeRefs);
    }

    /**
     * Implements.
     *
     * @param children containing the children. May include: a Comment, several TypeReference (as
     *        references to the supertypes)
     *
     */
    public Implements(ExtList children) {
        super(children);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnImplements(this);
    }
}
