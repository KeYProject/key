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
