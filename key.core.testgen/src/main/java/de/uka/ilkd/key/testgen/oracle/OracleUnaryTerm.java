/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

public record OracleUnaryTerm(OracleTerm sub, Op op) implements OracleTerm {
    public enum Op {
        Neg("!"), Minus("-");

        public final String symbol;

        Op(String symbol) {
            this.symbol = symbol;
        }

    }

    public String toString() {
        return op.symbol + sub;
    }
}
