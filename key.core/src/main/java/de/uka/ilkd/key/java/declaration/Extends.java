/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Extends.
 *
 * @author <TT>AutoDoc</TT>
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

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May include: several
     *        TypeReference (as references to the supertypes) a Comment
     */
    public Extends(ExtList children) {
        super(children);
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
