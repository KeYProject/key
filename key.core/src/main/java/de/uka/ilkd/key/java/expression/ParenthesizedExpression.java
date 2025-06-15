/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

/**
 * Redundant Parentheses. Modelled as a special "identity" unary "infix" operator.
 */

public class ParenthesizedExpression extends Operator
        implements ExpressionStatement, ReferencePrefix {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. In this case the order of
     *        the children is IMPORTANT. May contain: several of Expression (should be one, the
     *        first is taken as parenthesized expression), Comments
     */
    public ParenthesizedExpression(@NonNull ExtList children) {
        super(children);
    }

    public ParenthesizedExpression(Expression child) {
        super(child);
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

    public @NonNull SourceElement getFirstElement() {
        return this;
    }

    public @NonNull SourceElement getLastElement() {
        return this;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(@NonNull Visitor v) {
        v.performActionOnParenthesizedExpression(this);
    }

    /**
     * We do not have a prefix, so fake it! This way we implement ReferencePrefix
     *
     * @author VK
     */
    public @NonNull ReferencePrefix getReferencePrefix() {
        return null;
    }

    public @NonNull ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    public @NonNull KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getExpressionAt(0).getKeYJavaType(javaServ, ec);
    }


}
