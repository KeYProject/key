/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import com.github.javaparser.ast.Modifier;

import static com.github.javaparser.ast.Modifier.DefaultKeyword.*;

/**
 * Enum to wrap all current jml modifiers to avoid having to work with strings.
 */
public enum JMLModifier {
    ABSTRACT("abstract", Modifier.DefaultKeyword.ABSTRACT),
    FINAL("final", Modifier.DefaultKeyword.FINAL),
    GHOST("ghost", JML_GHOST),
    HELPER("helper", JML_HELPER),
    INSTANCE("instance", JML_INSTANCE),
    MODEL("model", JML_MODEL), NON_NULL("non_null", JML_NON_NULL),
    NULLABLE("nullable", JML_NULLABLE),
    NULLABLE_BY_DEFAULT("nullable_by_default", JML_NULLABLE_BY_DEFAULT),
    PRIVATE("private", Modifier.DefaultKeyword.PRIVATE),
    PROTECTED("protected", Modifier.DefaultKeyword.PROTECTED),
    PUBLIC("public", Modifier.DefaultKeyword.PUBLIC), PURE("pure", JML_PURE),
    STRICTLY_PURE("strictly_pure", JML_STRICTLY_PURE),
    SPEC_PROTECTED("spec_protected", JML_SPEC_PROTECTED),
    SPEC_PUBLIC("spec_public", JML_SPEC_PUBLIC), STATIC("static", Modifier.DefaultKeyword.STATIC),
    TWO_STATE("two_state", JML_TWO_STATE), NO_STATE("no_state", JML_NO_STATE),
    SPEC_JAVA_MATH("spec_java_math", JML_SPEC_JAVA_MATH),
    SPEC_SAFE_MATH("spec_safe_math", JML_SPEC_SAFE_MATH),
    SPEC_BIGINT_MATH("spec_bigint_math", JML_SPEC_BIGINT_MATH),
    CODE_JAVA_MATH("code_java_math", JML_CODE_JAVA_MATH),
    CODE_SAFE_MATH("code_safe_math", JML_CODE_SAFE_MATH),
    CODE_BIGINT_MATH("code_bigint_math", JML_CODE_BIGINT_MATH);

    /**
     * the modifier
     */
    private final String name;
    private final Modifier.DefaultKeyword parserKeyword;

    /**
     * enum constructor
     */
    JMLModifier(String name, Modifier.DefaultKeyword parserKeyword) {
        this.name = name;
        this.parserKeyword = parserKeyword;
    }

    @Override
    public String toString() {
        return this.name;
    }

    public Modifier.DefaultKeyword getParserKeyword() {
        return parserKeyword;
    }
}
