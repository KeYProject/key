/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;


import java.util.List;

import de.uka.ilkd.key.smt.model.Model;

import com.squareup.javapoet.TypeName;
import org.jspecify.annotations.Nullable;

import static com.squareup.javapoet.TypeName.*;

public class TestgenUtils {
    // setter and getter methods will be created for these types.
    public static final List<TypeName> PRIMITIVE_TYPES =
        List.of(BYTE, INT, LONG, CHAR, BOOLEAN, FLOAT, SHORT, DOUBLE);

    public static boolean isNumericType(String type) {
        return type.equals("byte") || type.equals("short") || type.equals("int")
                || type.equals("long") || type.equals("float") || type.equals("double");
    }

    public static boolean isPrimitiveType(String type) {
        return isNumericType(type) || type.equals("boolean") || type.equals("char");
    }

    public static boolean isPrimitiveType(TypeName type) {
        return PRIMITIVE_TYPES.contains(type);
    }

    public static String translateValueExpression(String val) {
        if (val.contains("/")) {
            val = val.substring(0, val.indexOf('/'));
        }
        if (val.equals("#o0")) {
            return "null";
        }
        val = val.replace("|", "");
        val = val.replace("#", "_");
        return val;
    }

    public static boolean filterVal(String s) {
        return !s.startsWith("#a") && !s.startsWith("#s") && !s.startsWith("#h")
                && !s.startsWith("#l") && !s.startsWith("#f");
    }

    public static boolean modelIsOK(@Nullable Model m) {
        return m != null && !m.isEmpty() && m.getHeaps() != null && !m.getHeaps().isEmpty()
                && m.getTypes() != null;
    }
}
