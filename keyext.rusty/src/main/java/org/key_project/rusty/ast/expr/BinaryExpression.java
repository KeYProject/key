/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record BinaryExpression(Operator op, Expr left, Expr right) implements Expr {
    @Override
    public Type type(Services services) {
        return null;
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public SyntaxElement getChild(int n) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    public enum Operator implements RustyProgramElement {
        Add("+"),
        Sub("-"),
        Mul("-"),
        Div("/"),
        Rem("%"),
        And("&&"),
        Or("||"),
        BitXor("^"),
        BitAnd("&"),
        BitOr("|"),
        Shl("<<"),
        Shr(">>"),
        Eq("=="),
        Lt("<"),
        Le("<="),
        Ne("!="),
        Ge(">="),
        Gt(">");

        private final String symbol;

        Operator(String s) {
            symbol = s;
        }

        @Override
        public String toString() {
            return symbol;
        }

        @Override
        public void visit(Visitor v) {

        }

        @Override
        public @NonNull SyntaxElement getChild(int n) {
            throw new IndexOutOfBoundsException("Operator has no children");
        }

        @Override
        public int getChildCount() {
            return 0;
        }
    }}
