/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.testgen.oracle;

public record OracleBinTerm(String op, OracleTerm left, OracleTerm right) implements OracleTerm {
    public String toString() {
        return "(%s %s %s)".formatted(left, op, right);
    }
}
