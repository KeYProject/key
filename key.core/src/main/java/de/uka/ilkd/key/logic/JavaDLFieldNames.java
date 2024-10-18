/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;


import org.key_project.logic.Name;

import org.jspecify.annotations.Nullable;

public class JavaDLFieldNames {
    public static final char FIELD_PREFIX = '#';
    public static final char IMPLICIT_NAME_PREFIX = '$';
    public static final String SEPARATOR = "::";
    private static final String FIELD_INFIX = SEPARATOR + FIELD_PREFIX;
    private static final String IMPLICIT_FIELD_INFIX =
        SEPARATOR + FIELD_PREFIX + IMPLICIT_NAME_PREFIX;

    private JavaDLFieldNames() {}

    public static boolean isField(Name name) {
        return isField(name.toString());
    }

    public static boolean isField(String name) {
        return name.contains(FIELD_INFIX);
    }

    public static boolean isImplicitField(Name name) {
        return name.toString().contains(IMPLICIT_FIELD_INFIX);
    }

    public static boolean isImplicit(ProgramElementName name) {
        return !name.getProgramName().isEmpty()
                && name.getProgramName().charAt(0) == IMPLICIT_NAME_PREFIX;
    }

    public static String toJava(String name) {
        return name.replace(FIELD_INFIX, SEPARATOR);
    }

    public static String toJava(Name name) {
        return toJava(name.toString());
    }

    public static String toJavaDL(Name name) {
        return toJavaDL(name.toString());
    }

    public static String toJavaDL(String name) {
        int index = name.indexOf(SEPARATOR);
        assert index > 0;
        return name.substring(0, index) + FIELD_INFIX + name.substring(index + 2);
    }

    public static ParsedFieldName split(String name) {
        int index = name.indexOf(SEPARATOR);
        if (index == -1) { return new ParsedFieldName(null, name); }
        return new ParsedFieldName(name.substring(0, index), name.substring(index + 2));
    }

    public record ParsedFieldName(@Nullable String scope, String name) {
        public String nameWithoutFieldPrefix() {
            if (!name.isEmpty() && name.charAt(0) == JavaDLFieldNames.FIELD_PREFIX) { return name.substring(1); }
            return name;
        }
    }
}
