/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

/**
 * Redundant Parentheses. Modelled as a special "identity" unary "infix" operator.
 */

public class ParenthesizedExpression extends Operator
        implements ExpressionStatement, ReferencePrefix {

    public ParenthesizedExpression(Expression child) {
        this(null, null, child);
    }

    public ParenthesizedExpression(@Nullable PositionInfo pi, @Nullable List<Comment> c, Expression expr) {
        super(pi, c, new ImmutableArray<>(expr));
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */
    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */
    public int getPrecedence() {
        return 0;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */
    public int getNotation() {
        return INFIX;
        /* Only unary infix operator;) */
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnParenthesizedExpression(this);
    }

    /**
     * We do not have a prefix, so fake it! This way we implement ReferencePrefix
     *
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
        return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getExpressionAt(0).getKeYJavaType(javaServ, ec);
    }


}
