/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

public enum AssignmentKind {
    Copy(""),
    BinaryOr("|"),
    Divide("/"),
    ShiftLeft("<<"),
    UnsignedShiftRight(">>>"),
    Plus("+"),
    ShiftRight(">>"),
    Minus("-"),
    Modulo("%"),
    Times("*"),
    BinaryAnd("&"),
    BinaryXOr("^");

    public final String symbol;

    AssignmentKind(String symbol) {
        this.symbol = symbol;
    }
}
