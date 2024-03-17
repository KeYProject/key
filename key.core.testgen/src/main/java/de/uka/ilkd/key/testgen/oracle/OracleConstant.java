/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.sort.Sort;

public class OracleConstant implements OracleTerm {

    private final String value;

    private Sort sort;

    public static final OracleConstant TRUE = new OracleConstant("true", JavaDLTheory.FORMULA);
    public static final OracleConstant FALSE = new OracleConstant("false", JavaDLTheory.FORMULA);

    public OracleConstant(String value, Sort sort) {
        this.value = value;
        this.sort = sort;
    }

    public String getValue() {
        return value;
    }

    public Sort getSort() {
        return sort;
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public String toString() {
        return value;
    }


}
