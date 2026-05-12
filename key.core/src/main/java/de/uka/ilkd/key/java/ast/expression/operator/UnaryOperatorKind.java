/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.ast.expression.Operator;

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.04.26)
 */
public enum UnaryOperatorKind {
    LOGICAL_NOT("!", 1),
    NEGATIVE("-", 1),
    POSITIVE("+", 1),
    BINARY_NOT("~", 1),

    PRE_INCREMENT("++", 0),
    PRE_DECREMENT("--", 0),
    POST_INCREMENT("++", 0, Operator.POSTFIX),
    POST_DECREMENT("--", 0, Operator.POSTFIX);


    public final String symbol;
    public final int precedence;
    public final int notation;

    UnaryOperatorKind(String symbol, int precedence) {
        this(symbol, precedence, Operator.PREFIX);
    }

    UnaryOperatorKind(String symbol, int precedence, int notation) {
        this.symbol = symbol;
        this.notation = notation;
        this.precedence = precedence;
    }
}
