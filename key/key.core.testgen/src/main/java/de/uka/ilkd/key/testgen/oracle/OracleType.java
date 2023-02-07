/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public class OracleType implements OracleTerm {

    private Sort s;

    public OracleType(Sort s) {
        super();
        this.s = s;
    }

    public String toString() {

        return s.name().toString();

    }

}
