/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

/**
 * Enum to wrap all current jml modifiers to avoid having to work with strings.
 */
public enum JMLModifier {
    ABSTRACT("abstract"), FINAL("final"), GHOST("ghost"), HELPER("helper"), INSTANCE("instance"),
    MODEL("model"), NON_NULL("non_null"), NULLABLE("nullable"),
    NULLABLE_BY_DEFAULT("nullable_by_default"), PRIVATE("private"), PROTECTED("protected"),
    PUBLIC("public"), PURE("pure"), STRICTLY_PURE("strictly_pure"),
    SPEC_PROTECTED("spec_protected"), SPEC_PUBLIC("spec_public"), STATIC("static"),
    TWO_STATE("two_state"), NO_STATE("no_state"), SPEC_JAVA_MATH("spec_java_math"),
    SPEC_SAFE_MATH("spec_safe_math"), SPEC_BIGINT_MATH("spec_bigint_math"),
    CODE_JAVA_MATH("code_java_math"), CODE_SAFE_MATH("code_safe_math"),
    CODE_BIGINT_MATH("code_bigint_math");

    /** the modifier */
    private final String name;

    /** enum constructor */
    JMLModifier(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return this.name;
    }
}
