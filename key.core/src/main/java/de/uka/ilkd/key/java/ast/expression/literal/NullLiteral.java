/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.logic.Name;

/**
 * Null literal. Is used as singleton.
 */

public non-sealed class NullLiteral extends Literal {

    public static final NullLiteral NULL = new NullLiteral();

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     */
    public NullLiteral() {
        super();
    }

    public NullLiteral(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnNullLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getNullType();
    }

    @Override
    public Name getLDTName() {
        throw new UnsupportedOperationException("No LDT is linked to the null literal.");
    }

}