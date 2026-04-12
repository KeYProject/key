/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.logic.SyntaxElement;

import org.jspecify.annotations.NullMarked;

/**
 *
 *
 */
@NullMarked
public class Modifier extends JavaProgramElement {
    public static Modifier[] createModifierList(ModifierKind... modifierKind) {
        Modifier[] modifiers = new Modifier[modifierKind.length];
        for (int i = 0; i < modifierKind.length; i++) {
            modifiers[i] = new Modifier(modifierKind[i]);
        }
        return modifiers;
    }

    public ModifierKind getKind() {
        return keyword;
    }

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

        public boolean allowsInheritance() {
            return this == PUBLIC || this == PROTECTED || this == JML_PACKAGE;
        }
    }

    private final ModifierKind keyword;

    public Modifier(ModifierKind keyword) {
        this.keyword = keyword;
    }

    public Modifier(PositionInfo pi, List<Comment> c, ModifierKind keyword) {
        super(pi, c);
        this.keyword = keyword;
    }

    public String getText() {
        return keyword.asString();
    }

    public void visit(Visitor v) {
        v.performActionOnModifier(this);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(getClass() + " " + this + " has no children");
    }

    @Override
    public final boolean equals(Object o) {
        if (!(o instanceof Modifier modifier))
            return false;
        if (!super.equals(o))
            return false;

        return keyword.equals(modifier.keyword);
    }

    @Override
    public int computeHashCode() {
        int result = super.hashCode();
        result = 31 * result + keyword.hashCode();
        return result;
    }
}
