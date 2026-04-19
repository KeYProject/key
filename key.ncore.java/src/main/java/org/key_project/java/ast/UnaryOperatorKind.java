/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

public enum UnaryOperatorKind {
    LOGICAL_NOT("!", 1),
    NEGATIVE("-", 1),
    POSITIVE("+", 1),
    BINARY_NOT("~", 1),

    PRE_INCREMENT("++", 0),
    PRE_DECREMENT("--", 0),
    POST_INCREMENT("++", 0, POSTFIX),
    POST_DECREMENT("--", 0, POSTFIX);


    public final String symbol;
    public final int precedence;
    public final int notation;

    UnaryOperatorKind(String symbol, int precedence) {
        this(symbol, precedence, PREFIX);
    }

    UnaryOperatorKind(String symbol, int precedence, int notation) {
        this.symbol = symbol;
        this.notation = notation;
        this.precedence = precedence;
    }
}
