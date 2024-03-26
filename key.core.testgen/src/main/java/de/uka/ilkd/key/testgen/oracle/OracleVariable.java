/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import org.key_project.logic.sort.Sort;

public record OracleVariable(String name, Sort sort) implements OracleTerm {

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        OracleVariable other = (OracleVariable) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (sort == null) {
            return other.sort == null;
        } else {
            return sort.equals(other.sort);
        }
    }

    public String toString() {
        return name;
    }


}
