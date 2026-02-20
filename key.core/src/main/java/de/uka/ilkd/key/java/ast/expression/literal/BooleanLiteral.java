/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.ast.expression.literal;

import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.BooleanLDT;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;


/**
 * Boolean literal.
 *
 * @author <TT>AutoDoc</TT>
 */
public final class BooleanLiteral extends Literal {
    public static final BooleanLiteral TRUE = new BooleanLiteral(true);
    public static final BooleanLiteral FALSE = new BooleanLiteral(false);

    private final boolean value;

    public BooleanLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments,
            boolean value) {
        super(pi, comments);
        this.value = value;
    }

    /**
     * get boolean literal for the given <code>value</code>. This supports
     * use of single literals, but we do not force it.
     *
     * @param val
     *        a boolean specifying the literal to be returned
     * @return the BooleanLiteral representing <tt>val</tt>
     */
    public static BooleanLiteral getBooleanLiteral(boolean val) {
        return val ? TRUE : FALSE;
    }

    /**
     * Boolean literal.
     *
     * @param value
     *        a boolean value.
     */

    private BooleanLiteral(boolean value) {
        this((PositionInfo) null, null, value);
    }

    /**
     * Boolean literal.
     *
     * @param children
     *        list with all children
     *        May contain: Comments
     * @param value
     *        a boolean value.
     */
    public BooleanLiteral(ExtList children, boolean value) {
        super(children);
        this.value = value;
    }

    /**
     * Boolean literal.
     *
     * @param children
     *        list with all children
     * @param pos
     *        The source code position.
     * @param value
     *        a boolean value.
     */
    public BooleanLiteral(ExtList children, PositionInfo pos, boolean value) {
        super(children, pos);
        this.value = value;
    }

    /**
     * Boolean literal.
     *
     * @param pos
     *        The source code position.
     * @param value
     *        a boolean value.
     */
    public BooleanLiteral(PositionInfo pos, boolean value) {
        super(pos);
        this.value = value;
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public boolean getValue() {
        return value;
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public String getName() {
        return (value ? "true" : "false");
    }

    @Override
    protected int computeHashCode() {
        return 37 * super.computeHashCode() + (getValue() ? 0 : 1);
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        return ((BooleanLiteral) o).getValue() == getValue();
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnBooleanLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }

    @Override
    public Name getLDTName() {
        return BooleanLDT.NAME;
    }

}
