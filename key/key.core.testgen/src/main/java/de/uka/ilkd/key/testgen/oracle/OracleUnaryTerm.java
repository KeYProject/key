/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.testgen.oracle;

import java.util.HashMap;
import java.util.Map;

public class OracleUnaryTerm implements OracleTerm {



    public enum Op {
        Neg, Minus
    };

    public static String OP_NEG = "!";
    public static String OP_MINUS = "-";
    private static Map<Op, String> op2String;

    static {
        op2String = new HashMap<OracleUnaryTerm.Op, String>();
        op2String.put(Op.Neg, OP_NEG);
        op2String.put(Op.Minus, OP_MINUS);
    }


    private OracleTerm sub;
    private Op op;

    public OracleUnaryTerm(OracleTerm sub, Op op) {
        this.sub = sub;
        this.op = op;
    }



    public Op getOp() {
        return op;
    }



    public OracleTerm getSub() {
        return sub;
    }

    public String toString() {
        return op2String.get(op) + sub.toString();
    }
}
