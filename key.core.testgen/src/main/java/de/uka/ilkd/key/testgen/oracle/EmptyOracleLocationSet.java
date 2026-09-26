/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.testgen.oracle;

/**
 * @author Alexander Weigl
 * @version 1 (17.03.24)
 */
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
