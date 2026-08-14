/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import org.jspecify.annotations.Nullable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.05.26)
 */
public enum ModifierKind {
    DEFAULT("default"),
    PUBLIC("public"),
    PROTECTED("protected"),
    PRIVATE("private"),
    ABSTRACT("abstract"),
    STATIC("static"),
    FINAL("final"),
    TRANSIENT("transient"),
    VOLATILE("volatile"),
    SYNCHRONIZED("synchronized"),
    NATIVE("native"),
    STRICTFP("strictfp"),
    TRANSITIVE("transitive"),
    SEALED("sealed"),
    NON_SEALED("non-sealed"),
    // KEY
    JML_PACKAGE("package"),
    JML_PURE("pure"),
    JML_STRICTLY_PURE("strictly_pure"),
    JML_HELPER("helper"),
    JML_INSTANCE("instance"),
    JML_NULLABLE_BY_DEFAULT("nullable_by_default"),
    JML_NON_NULL("non_null"),
    JML_NULLABLE("nullable"),
    JML_GHOST("ghost"),
    JML_MODEL("model"),
    JML_SPEC_PUBLIC("spec_public"),
    JML_SPEC_PACKAGE("spec_package"),
    JML_SPEC_PROTECTED("spec_protected"),
    JML_SPEC_PRIVATE("spec_private"),
    JML_NO_STATE("no_state"),
    JML_TWO_STATE("two_state"),
    JML_NON_NULL_BY_DEFAULT("non_null_by_default"),
    JML_NON_NULL_ELEMENTS("nonnullelements"),
    JML_UNPARSABLE_MODIFIERS("<unparsable>"),
    JML_CODE_BIGINT_MATH("code_bigint_math"),
    JML_CODE_JAVA_MATH("code_java_math"),
    JML_CODE_SAFE_MATH("code_safe_math"),
    JML_SPEC_BIGINT_MATH("spec_bigint_math"),
    JML_SPEC_JAVA_MATH("spec_java_math"),
    JML_SPEC_SAFE_MATH("spec_safe_math"),
    JML_CODE("code"),
    JML_OT_PEER("peer"),
    JML_OT_REP("rep"),
    JML_OT_READ_ONLY("read_only");

    private final String codeRepresentation;

    ModifierKind(String codeRepresentation) {
        this.codeRepresentation = codeRepresentation;
    }

    /**
     * @return the Java keyword represented by this enum constant.
     */
    public String asString() {
        if (name().startsWith("JML_")) {
            return "/*@" + codeRepresentation + "*/";
        }
        return codeRepresentation;
    }

    public boolean isVisibility() {
        return switch (this) {
            case PUBLIC, PRIVATE, PROTECTED, JML_PACKAGE -> true;
            default -> false;
        };
    }

    /** Visibility order: public < protected < package-private < private */
    private static int visibilityLevel(@Nullable ModifierKind kind) {
        if (kind == null || kind == JML_PACKAGE) { // Java's package private is null
            return 2;
        }
        return switch (kind) {
            case PUBLIC -> 0;
            case PROTECTED -> 1;
            case PRIVATE -> 3;
            default -> throw new IllegalArgumentException("not a visibility: " + kind);
        };
    }

    /**
     * returns the more restrictive modifier: public < protected < package-private < private
     * TODO: as package private is modelled as null or JML_PACKAGE the returned value
     * depends on the order (a == null, b==JML_PACKAGE returns null, a and b swapped returns
     * JML_PACKAGE)
     * As long as we have the asymmetry with the modelling that cannot be solved cleanly
     *
     * @param a first modifier
     * @param b second modifier
     * @return the more restrictive modifier
     */
    public static @Nullable ModifierKind moreRestrictive(@Nullable ModifierKind a,
            @Nullable ModifierKind b) {
        return visibilityLevel(a) >= visibilityLevel(b) ? a : b;
    }

    public static boolean allowsInheritance(ModifierKind kind) {
        return kind == PUBLIC || kind == PROTECTED;
    }
}
