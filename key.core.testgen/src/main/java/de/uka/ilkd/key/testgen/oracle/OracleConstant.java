/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public record OracleConstant(String value, Sort sort) implements OracleTerm {
    public static final OracleConstant TRUE = new OracleConstant("true", Sort.FORMULA);
    public static final OracleConstant FALSE = new OracleConstant("false", Sort.FORMULA);

    public String toString() {
        return value;
    }
}
