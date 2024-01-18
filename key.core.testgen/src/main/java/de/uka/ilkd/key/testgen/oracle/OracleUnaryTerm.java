/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.HashMap;
import java.util.Map;

public record OracleUnaryTerm(OracleTerm sub,
                              de.uka.ilkd.key.testgen.oracle.OracleUnaryTerm.Op op) implements OracleTerm {


    public enum Op {
        Neg, Minus
    }

    public static final String OP_NEG = "!";
    public static final String OP_MINUS = "-";
    private static final Map<Op, String> op2String;

    static {
        op2String = new HashMap<>();
        op2String.put(Op.Neg, OP_NEG);
        op2String.put(Op.Minus, OP_MINUS);
    }


    public String toString() {
        return op2String.get(op) + sub;
    }
}
