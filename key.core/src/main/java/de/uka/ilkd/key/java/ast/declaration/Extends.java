/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

/**
 * Extends.
 */
public class Extends extends InheritanceSpecification {

    /**
     * Extends.
     *
     * @param supertype a type reference.
     */
    public Extends(TypeReference supertype) {
        super(supertype);
    }

    public Extends(ImmutableArray<TypeReference> types) {
        super(types);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnExtends(this);
    }
}
