/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

import java.util.HashSet;
import java.util.Set;

sealed interface OracleLocationSet {
    EmptyOracleLocationSet EMPTY = new EmptyOracleLocationSet();
    AllLocsLocationSet ALL_LOCS = new AllLocsLocationSet();

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


final class EmptyOracleLocationSet implements OracleLocationSet {
    @Override
    public boolean contains(OracleLocation l) {
        return false;
    }

    @Override
    public String toString() {
        return "Empty";

    }
}


final class AllLocsLocationSet implements OracleLocationSet {
    @Override
    public boolean contains(OracleLocation l) {
        return true;
    }

    @Override
    public String toString() {
        return "All";
    }
}
