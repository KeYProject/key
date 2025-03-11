/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import org.key_project.logic.sort.Sort;

public record OracleType(Sort s) implements OracleTerm {

    public String toString() {

        return s.name().toString();

    }

}
