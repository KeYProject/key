/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

public enum BinaryOperatorKind {
    DIVIDE(2, "/"),
    MODULO(2, "%"),
    TIMES(2, "*"),
    MINUS(3, "-"),
    PLUS(3, "+"),
    SUBTYPE(3, "<:"),

    SHIFT_LEFT(4, "<<"),
    SHIFT_RIGHT(4, ">>"),
    UNSIGNED_SHIFT_RIGHT(4, ">>>"),

    GREATER_OR_EQUALS(5, ">="),
    LESS_OR_EQUALS(5, "<="),
    GREATER_THAN(5, ">"),
    LESS_THAN(5, "<"),
    EQUALS(6, "=="),
    NOT_EQUALS(6, "!="),


    BINARY_AND(7, "&"),
    BINARY_XOR(8, "^"),
    BINARY_OR(9, "|"),
    LOGICAL_AND(10, "&&"),
    LOGICAL_OR(11, "||");


    public final int precedence;
    public final String symbol;

    BinaryOperatorKind(int precedence, String symbol) {
        this.precedence = precedence;
        this.symbol = symbol;
    }
}
