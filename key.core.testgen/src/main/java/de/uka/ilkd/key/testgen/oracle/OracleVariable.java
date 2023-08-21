/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public class OracleVariable implements OracleTerm {

    private final String name;

    private final Sort sort;

    public OracleVariable(String name, Sort sort) {
        this.name = name;
        this.sort = sort;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((name == null) ? 0 : name.hashCode());
        result = prime * result + ((sort == null) ? 0 : sort.hashCode());
        return result;
    }

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

    public String getName() {
        return name;
    }

    public Sort getSort() {
        return sort;
    }

    public String toString() {
        return name;
    }


}
