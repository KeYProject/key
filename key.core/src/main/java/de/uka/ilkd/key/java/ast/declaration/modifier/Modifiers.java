package de.uka.ilkd.key.java.ast.declaration.modifier;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.declaration.Modifier;

import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/3/26)
 */
public class Modifiers {
    public static class DEFAULT extends Modifier {
        public DEFAULT() {
        }

        public DEFAULT(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "default";
        }
    }

    public static class PUBLIC extends Modifier {
        public PUBLIC() {
        }

        public PUBLIC(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "public";
        }
    }

    public static class PROTECTED extends Modifier {
        public PROTECTED() {
        }

        public PROTECTED(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "protected";
        }
    }

    public static class PRIVATE extends Modifier {
        public PRIVATE() {
        }

        public PRIVATE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "private";
        }
    }

    public static class ABSTRACT extends Modifier {
        public ABSTRACT() {
        }

        public ABSTRACT(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "abstract";
        }
    }

    public static class STATIC extends Modifier {
        public STATIC() {
        }

        public STATIC(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "static";
        }
    }

    public static class FINAL extends Modifier {
        public FINAL() {
        }

        public FINAL(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "final";
        }
    }

    public static class TRANSIENT extends Modifier {
        public TRANSIENT() {
        }

        public TRANSIENT(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "transient";
        }
    }

    public static class VOLATILE extends Modifier {
        public VOLATILE() {
        }

        public VOLATILE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "volatile";
        }
    }

    public static class SYNCHRONIZED extends Modifier {
        public SYNCHRONIZED() {
        }

        public SYNCHRONIZED(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "synchronized";
        }
    }

    public static class NATIVE extends Modifier {
        public NATIVE() {
        }

        public NATIVE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "native";
        }
    }

    public static class STRICTFP extends Modifier {
        public STRICTFP() {
        }

        public STRICTFP(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "strictfp";
        }
    }

    public static class TRANSITIVE extends Modifier {
        public TRANSITIVE() {
        }

        public TRANSITIVE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "transitive";
        }
    }

    public static class SEALED extends Modifier {
        public SEALED() {
        }

        public SEALED(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "sealed";
        }
    }

    public static class NON_SEALED extends Modifier {
        public NON_SEALED() {
        }

        public NON_SEALED(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "non-sealed";
        }
    }

    public static class JML_PACKAGE extends Modifier {
        public JML_PACKAGE() {
        }

        public JML_PACKAGE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "package";
        }
    }

    public static class JML_PURE extends Modifier {
        public JML_PURE() {
        }

        public JML_PURE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "pure";
        }
    }

    public static class JML_STRICTLY_PURE extends Modifier {
        public JML_STRICTLY_PURE() {
        }

        public JML_STRICTLY_PURE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "strictly_pure";
        }
    }

    public static class JML_HELPER extends Modifier {
        public JML_HELPER() {
        }

        public JML_HELPER(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "helper";
        }
    }

    public static class JML_INSTANCE extends Modifier {
        public JML_INSTANCE() {
        }

        public JML_INSTANCE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "instance";
        }
    }

    public static class JML_NULLABLE_BY_DEFAULT extends Modifier {
        public JML_NULLABLE_BY_DEFAULT() {
        }

        public JML_NULLABLE_BY_DEFAULT(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "nullable_by_default";
        }
    }

    public static class JML_NON_NULL extends Modifier {
        public JML_NON_NULL() {
        }

        public JML_NON_NULL(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "non_null";
        }
    }

    public static class JML_NULLABLE extends Modifier {
        public JML_NULLABLE() {
        }

        public JML_NULLABLE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "nullable";
        }
    }

    public static class JML_GHOST extends Modifier {
        public JML_GHOST() {
        }

        public JML_GHOST(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "ghost";
        }
    }

    public static class JML_MODEL extends Modifier {
        public JML_MODEL() {
        }

        public JML_MODEL(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "model";
        }
    }

    public static class JML_SPEC_PUBLIC extends Modifier {
        public JML_SPEC_PUBLIC() {
        }

        public JML_SPEC_PUBLIC(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_public";
        }
    }

    public static class JML_SPEC_PACKAGE extends Modifier {
        public JML_SPEC_PACKAGE() {
        }

        public JML_SPEC_PACKAGE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_package";
        }
    }

    public static class JML_SPEC_PROTECTED extends Modifier {
        public JML_SPEC_PROTECTED() {
        }

        public JML_SPEC_PROTECTED(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_protected";
        }
    }

    public static class JML_SPEC_PRIVATE extends Modifier {
        public JML_SPEC_PRIVATE() {
        }

        public JML_SPEC_PRIVATE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_private";
        }
    }

    public static class JML_NO_STATE extends Modifier {
        public JML_NO_STATE() {
        }

        public JML_NO_STATE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "no_state";
        }
    }

    public static class JML_TWO_STATE extends Modifier {
        public JML_TWO_STATE() {
        }

        public JML_TWO_STATE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "two_state";
        }
    }

    public static class JML_NON_NULL_BY_DEFAULT extends Modifier {
        public JML_NON_NULL_BY_DEFAULT() {
        }

        public JML_NON_NULL_BY_DEFAULT(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "non_null_by_default";
        }
    }

    public static class JML_NON_NULL_ELEMENTS extends Modifier {
        public JML_NON_NULL_ELEMENTS() {
        }

        public JML_NON_NULL_ELEMENTS(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "nonnullelements";
        }
    }

    public static class JML_UNPARSABLE_MODIFIERS extends Modifier {
        public JML_UNPARSABLE_MODIFIERS() {
        }

        public JML_UNPARSABLE_MODIFIERS(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "<unparsable>";
        }
    }

    public static class JML_CODE_BIGINT_MATH extends Modifier {
        public JML_CODE_BIGINT_MATH() {
        }

        public JML_CODE_BIGINT_MATH(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "code_bigint_math";
        }
    }

    public static class JML_CODE_JAVA_MATH extends Modifier {
        public JML_CODE_JAVA_MATH() {
        }

        public JML_CODE_JAVA_MATH(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "code_java_math";
        }
    }

    public static class JML_CODE_SAFE_MATH extends Modifier {
        public JML_CODE_SAFE_MATH() {
        }

        public JML_CODE_SAFE_MATH(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "code_safe_math";
        }
    }

    public static class JML_SPEC_BIGINT_MATH extends Modifier {
        public JML_SPEC_BIGINT_MATH() {
        }

        public JML_SPEC_BIGINT_MATH(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_bigint_math";
        }
    }

    public static class JML_SPEC_JAVA_MATH extends Modifier {
        public JML_SPEC_JAVA_MATH() {
        }

        public JML_SPEC_JAVA_MATH(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_java_math";
        }
    }

    public static class JML_SPEC_SAFE_MATH extends Modifier {
        public JML_SPEC_SAFE_MATH() {
        }

        public JML_SPEC_SAFE_MATH(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "spec_safe_math";
        }
    }

    public static class JML_CODE extends Modifier {
        public JML_CODE() {
        }

        public JML_CODE(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "code";
        }
    }

    public static class JML_OT_PEER extends Modifier {
        public JML_OT_PEER() {
        }

        public JML_OT_PEER(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "peer";
        }
    }

    public static class JML_OT_REP extends Modifier {
        public JML_OT_REP() {
        }

        public JML_OT_REP(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "rep";
        }
    }

    public static class JML_OT_READ_ONLY extends Modifier {
        public JML_OT_READ_ONLY() {
        }

        public JML_OT_READ_ONLY(PositionInfo pi, List<Comment> c) {
            super(pi, c);
        }

        protected String getSymbol() {
            return "read_only";
        }
    }
    
    public static void main(String[] args) {
        String s = """
                    public static class Nullable extends Modifier {
                    public Nullable() {}
                    public Nullable(PositionInfo pi, List<Comment> c) {
                        super(pi, c);
                    }
                    protected String getSymbol() {
                        return "two_state";
                    }
                }
                """;
        for (var value : com.github.javaparser.ast.Modifier.DefaultKeyword.values()) {
            System.out.println(s.replace("Nullable", value.name())
                    .replace("two_state", value.asString()));
        }
    }
}
