/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.smt.model.Model;
import org.jspecify.annotations.Nullable;

public class TestgenUtils {
    interface AssignmentCreator {
        String assign(String type, Object left, String right);
    }

    public String createAssignment(boolean rfl, String type, Object left, String right) {
        if (rfl) {
            return createAssignmentWithRfl(type, left, right);
        } else {
            return createAssignmentWithoutRfl(type, left, right);
        }
    }

    public static String createAssignmentWithRfl(String type, Object left, String right) {
        if (left instanceof RefEx leftEx) {
            return "%s.%s%s(%s.class, %s, \"%s\", %s)".formatted(
                    ReflectionClassCreator.NAME_OF_CLASS,
                    ReflectionClassCreator.SET_PREFIX,
                    ReflectionClassCreator.cleanTypeName(leftEx.fieldType()),
                    leftEx.rcObjType(), leftEx.rcObj(), leftEx.field(), right);
        } else {
            return createAssignmentWithoutRfl(type, left, right);
        }
    }

    public static String createAssignmentWithoutRfl(String type, Object left, String right) {
        return "%s %s = %s".formatted(type, left, right);
    }

    public static boolean isNumericType(String type) {
        return type.equals("byte") || type.equals("short") || type.equals("int")
                || type.equals("long") || type.equals("float") || type.equals("double");
    }

    public static boolean isPrimitiveType(String type) {
        return isNumericType(type) || type.equals("boolean") || type.equals("char");
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
