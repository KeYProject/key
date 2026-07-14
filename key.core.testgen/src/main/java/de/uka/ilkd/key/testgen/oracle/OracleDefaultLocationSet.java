/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.HashSet;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (17.03.24)
 */
final class OracleDefaultLocationSet implements OracleLocationSet {
    final Set<OracleLocation> locs = new HashSet<>();

    void add(OracleLocation loc) {
        locs.add(loc);
    }

    void add(OracleLocationSet loc) {
        if (loc instanceof OracleDefaultLocationSet o)
            locs.addAll(o.locs);
    }

    @Override
    public boolean contains(OracleLocation l) {
        for (OracleLocation loc : locs) {
            if (loc.equals(l)) {
                return true;
            }

            if (loc.isAllFields() && loc.object().equals(l.object())) {
                return true;
            }
        }
        return false;
    }

    public String toString() {
        StringBuilder result = new StringBuilder();

        result.append("{");

        for (OracleLocation loc : locs) {
            result.append(loc).append(" ");
        }

        result.append("}");


        return result.toString();


    }

}
