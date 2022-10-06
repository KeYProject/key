package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.logic.Name;

public enum JMLModifier {
    ABSTRACT("abstract"), FINAL("final"), GHOST("ghost"), HELPER("helper"), INSTANCE("instance"),
    MODEL("model"), NON_NULL("non_null"), NULLABLE("nullable"),
    NULLABLE_BY_DEFAULT("nullable_by_default"), PRIVATE("private"), PROTECTED("protected"),
    PUBLIC("public"), PURE("pure"), STRICTLY_PURE("strictly_pure"),
    SPEC_PROTECTED("spec_protected"), SPEC_PUBLIC("spec_public"), STATIC("static"),
    TWO_STATE("two_state"), NO_STATE("no_state"), SPEC_JAVA_MATH("spec_java_math"),
    SPEC_SAVE_MATH("spec_save_math"), SPEC_BIGINT_MATH("spec_bigint_math"),
    CODE_JAVA_MATH("code_java_math"), CODE_SAVE_MATH("code_save_math"),
    CODE_BIGINT_MATH("code_bigint_math");

    private final Name name;

    JMLModifier(String name) {
        this.name = new Name(name);
    }


    @Override
    public String toString() {
        return this.name.toString();
    }
}
