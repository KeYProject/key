/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import org.jspecify.annotations.Nullable;

/**
 * Mapping between Java's primitive types and their boxed wrapper types, plus the primitive
 * widening rules needed by the autoboxing transformation.
 * <p>
 * The names are the Java names, so {@code int} maps to {@code java.lang.Integer}. Boxing only ever
 * converts a value whose primitive type already matches the wrapper's primitive type (JLS 5.1.7);
 * widening before boxing is not a conversion Java allows.
 */
public enum WrapperType {
    BOOLEAN("boolean", "java.lang.Boolean"),
    BYTE("byte", "java.lang.Byte"),
    SHORT("short", "java.lang.Short"),
    CHAR("char", "java.lang.Character"),
    INT("int", "java.lang.Integer"),
    LONG("long", "java.lang.Long"),
    FLOAT("float", "java.lang.Float"),
    DOUBLE("double", "java.lang.Double");

    private final String primitiveName;
    private final String wrapperName;
    private final String simpleWrapperName;

    WrapperType(String primitiveName, String wrapperName) {
        this.primitiveName = primitiveName;
        this.wrapperName = wrapperName;
        this.simpleWrapperName = wrapperName.substring(wrapperName.lastIndexOf('.') + 1);
    }

    /** The Java name of the primitive type, for example {@code int}. */
    public String primitiveName() {
        return primitiveName;
    }

    /** The fully qualified name of the wrapper type, for example {@code java.lang.Integer}. */
    public String wrapperName() {
        return wrapperName;
    }

    /** The simple name of the wrapper type, for example {@code Integer}. */
    public String simpleWrapperName() {
        return simpleWrapperName;
    }

    /** The name of the field holding the primitive value. */
    public String valueFieldName() {
        return "value";
    }

    /**
     * Returns the wrapper for a primitive Java name, or {@code null} if the name is not a
     * primitive type.
     */
    public static @Nullable WrapperType forPrimitive(String primitiveName) {
        for (WrapperType type : values()) {
            if (type.primitiveName.equals(primitiveName)) {
                return type;
            }
        }
        return null;
    }

    /**
     * Returns the wrapper for a fully qualified wrapper name, or {@code null} if the name is not
     * one of the eight wrapper types.
     */
    public static @Nullable WrapperType forWrapper(String qualifiedName) {
        for (WrapperType type : values()) {
            if (type.wrapperName.equals(qualifiedName)) {
                return type;
            }
        }
        return null;
    }

    /**
     * Tells whether a primitive value of type {@code from} can be widened to {@code to} (JLS
     * 5.1.2). Identity counts as widening.
     */
    public static boolean isWidening(String from, String to) {
        if (from.equals(to)) {
            return true;
        }
        return switch (from) {
            case "byte" -> switch (to) {
                case "short", "int", "long", "float", "double" -> true;
                default -> false;
            };
            case "short", "char" -> switch (to) {
                case "int", "long", "float", "double" -> true;
                default -> false;
            };
            case "int" -> switch (to) {
                case "long", "float", "double" -> true;
                default -> false;
            };
            case "long" -> switch (to) {
                case "float", "double" -> true;
                default -> false;
            };
            case "float" -> to.equals("double");
            default -> false;
        };
    }
}
