/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import static de.uka.ilkd.key.testgen.oracle.OracleLocationSets.ALL_LOCS;
import static de.uka.ilkd.key.testgen.oracle.OracleLocationSets.EMPTY;

public sealed

interface OracleLocationSet
permits AllLocsLocationSet, EmptyOracleLocationSet, OracleDefaultLocationSet
{

    static OracleLocationSet singleton(OracleLocation loc) {
        var result = new OracleDefaultLocationSet();
        result.add(loc);
        return result;
    }

    static OracleLocationSet union(OracleLocationSet l1, OracleLocationSet l2) {
        if (l1 == ALL_LOCS || l2 == ALL_LOCS) {
            return ALL_LOCS;
        }

        if (l1 == EMPTY) {
            return l2;
        }

        if (l2 == EMPTY) {
            return l1;
        }

        var result = new OracleDefaultLocationSet();
        result.add(l1);
        result.add(l2);
        return result;
    }

    static OracleLocationSet intersect(OracleLocationSet l1, OracleLocationSet l2) {
        if (l1 == EMPTY || l2 == EMPTY) {
            return EMPTY;
        }

        if (l1 == ALL_LOCS) {
            return l2;
        }

        if (l2 == ALL_LOCS) {
            return l1;
        }


        var s1 = (OracleDefaultLocationSet) l1;
        var s2 = (OracleDefaultLocationSet) l2;

        var result = new OracleDefaultLocationSet();
        for (OracleLocation l : s1.locs) {
            if (l2.contains(l)) {
                result.add(l);
            }
        }

        for (OracleLocation l : s2.locs) {
            if (l1.contains(l)) {
                result.add(l);
            }
        }

        return result;
    }

    boolean contains(OracleLocation l);
}
