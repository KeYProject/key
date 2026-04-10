/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.oracle;

public record OracleLocation(String object, String field) {
    public static final String ALL_FIELDS = "<allFields>";

    public OracleLocation(String object) {
        this(object, ALL_FIELDS);
    }

    public boolean isAllFields() {
        return field.equals(ALL_FIELDS);
    }

    public String toString() {
        if (field.startsWith("[")) {
            return object + field;
        } else {
            return object + "." + field;
        }
    }
}
