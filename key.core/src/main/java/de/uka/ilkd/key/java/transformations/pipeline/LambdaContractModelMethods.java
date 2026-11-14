/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.java.transformations.pipeline.lambda.ClauseText;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.LambdaContractSpec;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.LambdaContractSpec.Clause;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.LambdaContractSpec.ClauseKind;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLFieldDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.njml.PreParser;

import org.key_project.util.collection.ImmutableList;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.jml.doc.JmlDoc;
import com.github.javaparser.ast.jml.doc.JmlDocDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Converts the JML contract of a desugared lambda expression (or method reference) into JML
 * model methods (and, for the frame clauses, optionally model fields) as specified by Csiky's
 * thesis, Def. 7 and Table 6.1:
 * <pre>
 *   requires pre;      -&gt;  /*@ model boolean preCondition(args) { return cb(pre); } @*&#47;
 *   ensures post;      -&gt;  /*@ model ... postCondition(args, R __result) { return cb(post); } @*&#47;
 *   invariant inv;     -&gt;  /*@ model ... invariantMethod(args, R __result) { return cb(inv); } @*&#47;
 *   assignable frame;  -&gt;  /*@ model \locset frameCondition(args) { return \locset(cb(frame)); } @*&#47;
 *   accessible acc;    -&gt;  /*@ model \locset accessibleMethod(args) { return \locset(cb(acc)); } @*&#47;
 * </pre>
 * <p>
 * The clause-to-model-method mapping comes from the functional interface: the conversion
 * checks that the functional interface declares the corresponding abstract model method (or
 * model field for the frame clauses) and takes the return type and the {@code two_state}
 * modifier from that declaration. If nothing matches, the conversion reports an error
 * (cs = &perp;).
 * <p>
 * The clause bodies are rewritten ({@code cb}) so that they refer to the members of the
 * desugared class: {@code \result} becomes the {@code __result} parameter, the keywords
 * {@code this}/{@code super} become the {@code outer_this}/{@code outer_super} fields, and
 * free variables become either the captured {@code _outer_final_&lt;name&gt;} field or an
 * access {@code outer_this.&lt;name&gt;} on the enclosing instance.
 * <p>
 * This step must run after {@link LocalClassTransformation} (which hoists the desugared local
 * classes and introduces the {@code _outer_final_*}, {@code outer_this} fields) and before
 * {@link JMLTransformer} (which turns the emitted JML model methods into KeY-representable
 * declarations).
 *
 * @author weigl
 */
public class LambdaContractModelMethods extends JavaTransformerAbstract {

    /** Name of the injected result parameter of postCondition/invariantMethod (Def. 7). */
    private static final String RESULT_PARAM = "__result";

    public LambdaContractModelMethods(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        for (ClassOrInterfaceDeclaration cls : cu.findAll(ClassOrInterfaceDeclaration.class)) {
            if (!cls.containsData(LambdaContractSpec.KEY)) {
                continue;
            }
            LambdaContractSpec spec = cls.getData(LambdaContractSpec.KEY);
            if (spec == null) {
                continue;
            }
            convert(cls, spec);
            // Consume the contract so that the step is idempotent if it is ever re-applied.
            cls.setData(LambdaContractSpec.KEY, null);
        }
    }

    // --------------------------------------------------------------------------------
    // Contract conversion (Def. 7)
    // --------------------------------------------------------------------------------

    private void convert(ClassOrInterfaceDeclaration cls, LambdaContractSpec spec) {
        TypeDeclaration<?> fi = resolveFunctionalInterface(cls);
        if (fi == null) {
            throw reportError(cls, "Cannot resolve the functional interface of the generated "
                + "class for its lambda contract");
        }
        FiMembers members = parseFiMembers(fi, cls);
        MethodDeclaration sam = findSam(cls, fi);
        if (sam == null) {
            throw reportError(cls, "Cannot find the functional method of the generated class "
                + "for its lambda contract");
        }
        for (Clause clause : spec.clauses()) {
            RewriteContext ctx = new RewriteContext(cls, sam);
            List<String> texts = emit(clause, members, sam, ctx, cls);
            for (String text : texts) {
                validateAndAttach(cls, text);
            }
        }
    }

    private List<String> emit(Clause clause, FiMembers members, MethodDeclaration sam,
            RewriteContext ctx, ClassOrInterfaceDeclaration cls) {
        return switch (clause.kind()) {
            case REQUIRES ->
                List.of(modelMethodText("preCondition", clause, false, members, sam, ctx, cls));
            case ENSURES ->
                List.of(modelMethodText("postCondition", clause, true, members, sam, ctx, cls));
            case INVARIANT ->
                List.of(modelMethodText("invariantMethod", clause, true, members, sam, ctx, cls));
            case ASSIGNABLE, ACCESSIBLE -> frameText(clause, members, sam, ctx, cls);
        };
    }

    /**
     * The model method route of Def. 7 for a predicate clause (requires/ensures/invariant): the
     * return type and {@code two_state} modifier are taken from the model method declared by the
     * functional interface.
     */
    private String modelMethodText(String name, Clause clause, boolean takesResult,
            FiMembers members, MethodDeclaration sam, RewriteContext ctx,
            ClassOrInterfaceDeclaration cls) {
        FiMethod m = members.methods.get(name);
        if (m == null) {
            throw reportError(cls, "The functional interface does not declare the model method "
                + "%s that the %s clause of the lambda requires (Def. 7)",
                name, keyword(clause.kind()));
        }
        String params = samParams(sam, takesResult ? sam.getType().asString() + " " + RESULT_PARAM
                : null);
        String body = ctx.cb(clause.expression());
        return "model%s %s %s(%s) { return %s; }".formatted(
            m.twoState() ? " two_state" : "", m.returnType(), name, params, body);
    }

    /**
     * The frame clauses (assignable/accessible) are converted into a model method
     * {@code frameCondition}/{@code accessibleMethod}, or -- if the functional interface
     * declares a model field {@code footprint}/{@code accessibleFields} instead -- into such a
     * field together with a {@code represents} clause (Def. 7, Table 6.1).
     */
    private List<String> frameText(Clause clause, FiMembers members, MethodDeclaration sam,
            RewriteContext ctx, ClassOrInterfaceDeclaration cls) {
        boolean assignable = clause.kind() == ClauseKind.ASSIGNABLE;
        String methodName = assignable ? "frameCondition" : "accessibleMethod";
        String fieldName = assignable ? "footprint" : "accessibleFields";
        FiMethod m = members.methods.get(methodName);
        if (m != null) {
            // model method route: wrap the store reference into a locset expression
            String body = "\\locset(" + ctx.cb(clause.expression()) + ")";
            String params = samParams(sam, null);
            return List.of("model%s %s %s(%s) { return %s; }".formatted(
                m.twoState() ? " two_state" : "", m.returnType(), methodName, params, body));
        }
        String fieldType = members.fields.get(fieldName);
        if (fieldType != null) {
            // model field route; only valid if the clause does not depend on the arguments
            // of the functional method (Def. 7)
            if (usesSamParams(clause.expression(), sam)) {
                throw reportError(cls, "The %s clause of the lambda must not depend on the "
                    + "arguments of the functional method when the frame is stated as model "
                    + "field %s (Def. 7)", keyword(clause.kind()), fieldName);
            }
            String body = ctx.cb(clause.expression());
            return List.of("model " + fieldType + " " + fieldName + ";",
                "represents " + fieldName + " <- " + body + ";");
        }
        throw reportError(cls, "The functional interface declares neither a model method %s nor "
            + "a model field %s for the %s clause of the lambda (Def. 7)",
            methodName, fieldName, keyword(clause.kind()));
    }

    private static String keyword(ClauseKind kind) {
        return kind.name().toLowerCase(Locale.ROOT);
    }

    /** The parameters {@code T1 p1, T2 p2, ...} of the functional method, plus result. */
    private static String samParams(MethodDeclaration sam, @Nullable String resultParam) {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (Parameter p : sam.getParameters()) {
            if (!first) {
                sb.append(", ");
            }
            sb.append(p.getType().asString()).append(' ').append(p.getNameAsString());
            first = false;
        }
        if (resultParam != null) {
            if (!first) {
                sb.append(", ");
            }
            sb.append(resultParam);
        }
        return sb.toString();
    }

    private boolean usesSamParams(String expression, MethodDeclaration sam) {
        Set<String> names = new HashSet<>();
        for (Parameter p : sam.getParameters()) {
            names.add(p.getNameAsString());
        }
        for (ClauseText.Part p : ClauseText.parts(expression)) {
            if (p.identifier() && !p.prevDot() && names.contains(p.text())) {
                return true;
            }
        }
        return false;
    }

    // --------------------------------------------------------------------------------
    // Functional interface lookup
    // --------------------------------------------------------------------------------

    private @Nullable TypeDeclaration<?> resolveFunctionalInterface(
            ClassOrInterfaceDeclaration cls) {
        if (cls.getImplementedTypes().isEmpty()) {
            return null;
        }
        ClassOrInterfaceType it = cls.getImplementedTypes().get(0);
        // 1) a type of the same compilation unit
        var cu = cls.findCompilationUnit();
        if (cu.isPresent()) {
            TypeDeclaration<?> t = findType(cu.get(), it.getNameAsString());
            if (t != null) {
                return t;
            }
        }
        // 2) a type in another compilation unit of the program
        for (TypeDeclaration<?> td : cache.typeDeclarations()) {
            if (td.getNameAsString().equals(it.getNameAsString())) {
                return td;
            }
        }
        // 3) resolved via the symbol solver
        try {
            com.github.javaparser.resolution.types.ResolvedType rt = it.resolve();
            if (!rt.isReferenceType()) {
                return null;
            }
            Optional<com.github.javaparser.ast.Node> ast =
                rt.asReferenceType().getTypeDeclaration().flatMap(
                    com.github.javaparser.resolution.declarations.AssociableToAST::toAst);
            return ast.map(n -> n instanceof TypeDeclaration<?> t ? t : null).orElse(null);
        } catch (RuntimeException e) {
            return null;
        }
    }

    private static @Nullable TypeDeclaration<?> findType(Node root, String name) {
        for (TypeDeclaration<?> td : root.findAll(TypeDeclaration.class)) {
            if (td.getNameAsString().equals(name)) {
                return td;
            }
        }
        return null;
    }

    /**
     * The single abstract method of the functional interface, matched by name in the generated
     * class.
     */
    private @Nullable MethodDeclaration findSam(ClassOrInterfaceDeclaration cls,
            TypeDeclaration<?> fi) {
        String samName = null;
        for (MethodDeclaration m : fi.getMethods()) {
            if (!m.isStatic() && !m.isDefault() && !m.isPrivate()) {
                samName = m.getNameAsString();
                break;
            }
        }
        for (MethodDeclaration m : cls.getMethods()) {
            if (samName == null || m.getNameAsString().equals(samName)) {
                return m;
            }
        }
        return cls.getMethods().isEmpty() ? null : cls.getMethods().get(0);
    }

    // --------------------------------------------------------------------------------
    // Model members of the functional interface
    // --------------------------------------------------------------------------------

    /**
     * Parses all JML comments of the functional interface and collects the declared abstract
     * model methods and model fields (Def. 7: "The conversion checks that the model method or
     * field for a given clause is defined in the functional interface.").
     */
    private FiMembers parseFiMembers(TypeDeclaration<?> fi, Node where) {
        FiMembers result = new FiMembers();
        JmlDocSanitizer sanitizer = new JmlDocSanitizer(
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().getJmlEnabledKeys());
        for (BodyDeclaration<?> member : fi.getMembers()) {
            if (!(member instanceof JmlDocDeclaration jd)) {
                continue;
            }
            String text = sanitizer.asString(jd.getJmlComments());
            PreParser pp = TransformationPipelineServices.getPreParser();
            ImmutableList<TextualJMLConstruct> constructs;
            try {
                constructs = pp.parseClassLevel(text);
            } catch (RuntimeException e) {
                throw reportError(where, "Cannot parse the JML comments of the functional "
                    + "interface %s: %s", fi.getNameAsString(), e.getMessage());
            }
            services.addWarnings(pp.getWarnings());
            for (TextualJMLConstruct c : constructs) {
                ImmutableList<JMLModifier> mods = c.getModifiers();
                if (c instanceof TextualJMLMethodDecl md) {
                    if (mods.contains(JMLModifier.MODEL)) {
                        result.methods.put(md.getMethodName(),
                            new FiMethod(md.getDecl().typespec().getText(),
                                mods.contains(JMLModifier.TWO_STATE)));
                    }
                } else if (c instanceof TextualJMLFieldDecl fd) {
                    if (mods.contains(JMLModifier.MODEL)) {
                        result.fields.put(fd.getDecl().IDENT().getText(),
                            fd.getDecl().typespec().getText());
                    }
                }
            }
        }
        return result;
    }

    private record FiMethod(String returnType, boolean twoState) {
    }

    /** The model methods and model fields declared by the functional interface. */
    private static final class FiMembers {
        final Map<String, FiMethod> methods = new HashMap<>();
        final Map<String, String> fields = new HashMap<>();
    }

    // --------------------------------------------------------------------------------
    // Clause body rewriting (Def. 8 "cb")
    // --------------------------------------------------------------------------------

    /**
     * Rewriting context for the clause bodies of one generated class: the parameter names of
     * its functional method, the fields added by the hoisting (captured finals and outer
     * instances) and the fields of the physical enclosing type.
     */
    private static final class RewriteContext {
        private final ClassOrInterfaceDeclaration cls;
        private final Map<String, String> captured = new HashMap<>();
        private final Set<String> enclosingInstanceFields = new HashSet<>();
        private final Set<String> enclosingStaticFields = new HashSet<>();
        private final Set<String> samParams = new HashSet<>();
        @Nullable
        private String outerThis;
        @Nullable
        private String outerSuper;

        RewriteContext(ClassOrInterfaceDeclaration cls, MethodDeclaration sam) {
            this.cls = cls;
            for (Parameter p : sam.getParameters()) {
                samParams.add(p.getNameAsString());
            }
            for (FieldDeclaration fd : cls.getFields()) {
                for (VariableDeclarator v : fd.getVariables()) {
                    String n = v.getNameAsString();
                    if (n.startsWith(PipelineConstants.FINAL_VAR_PREFIX)) {
                        captured.put(n.substring(PipelineConstants.FINAL_VAR_PREFIX.length()), n);
                    } else if (n.equals("outer_this") || n.startsWith("outer_this_")) {
                        outerThis = n;
                    } else if (n.equals("outer_super") || n.startsWith("outer_super_")) {
                        outerSuper = n;
                    }
                }
            }
            Node parent = cls.getParentNode().orElse(null);
            if (parent instanceof TypeDeclaration<?> enclosing) {
                for (FieldDeclaration fd : enclosing.getFields()) {
                    for (VariableDeclarator v : fd.getVariables()) {
                        if (fd.isStatic()) {
                            enclosingStaticFields.add(v.getNameAsString());
                        } else {
                            enclosingInstanceFields.add(v.getNameAsString());
                        }
                    }
                }
            }
        }

        /**
         * Applies Def. 8 {@code cb} to a clause body. Reports an error if the body references a
         * variable that is neither a parameter of the functional method, nor a captured local, nor
         * an instance field of the enclosing type (cs = &perp;).
         */
        String cb(String expression) {
            StringBuilder sb = new StringBuilder();
            List<String> unresolved = new ArrayList<>();
            for (ClauseText.Part p : ClauseText.parts(expression)) {
                if (!p.identifier() || p.prevDot()) {
                    sb.append(p.text());
                    continue;
                }
                String t = p.text();
                if ("this".equals(t) || "super".equals(t)) {
                    String rep = "this".equals(t) ? outerThis : outerSuper;
                    if (rep == null) {
                        unresolved.add(t);
                        sb.append(t);
                    } else {
                        sb.append(rep);
                    }
                    continue;
                }
                if ("\\result".equals(t)) {
                    sb.append(RESULT_PARAM);
                    continue;
                }
                if (t.startsWith("\\")) {
                    // other JML escapes (\old, \nothing, ...) pass through
                    sb.append(t);
                    continue;
                }
                if (samParams.contains(t)) {
                    sb.append(t);
                    continue;
                }
                String capturedField = captured.get(t);
                if (capturedField != null) {
                    sb.append(capturedField);
                    continue;
                }
                if (enclosingInstanceFields.contains(t)) {
                    if (outerThis == null) {
                        unresolved.add(t);
                        sb.append(t);
                    } else {
                        sb.append(outerThis).append('.').append(t);
                    }
                    continue;
                }
                if (enclosingStaticFields.contains(t)) {
                    sb.append(t);
                    continue;
                }
                if (p.nextDot() || p.nextParen()) {
                    // a type or receiver name (followed by '.') or a method/operator name
                    // (followed by '(') that is no known variable: leave it verbatim
                    sb.append(t);
                    continue;
                }
                unresolved.add(t);
                sb.append(t);
            }
            if (!unresolved.isEmpty()) {
                throw reportError(cls,
                    "The lambda contract references variables that are neither parameters of "
                        + "the functional method, nor captured locals, nor fields of the "
                        + "enclosing type: %s",
                    unresolved);
            }
            return sb.toString();
        }
    }

    // --------------------------------------------------------------------------------
    // Emission and validation
    // --------------------------------------------------------------------------------

    /**
     * Validates the generated JML text by parsing it as a class-level JML construct before it
     * is attached to the class as a JML comment.
     */
    private void validateAndAttach(ClassOrInterfaceDeclaration cls, String text) {
        PreParser pp = TransformationPipelineServices.getPreParser();
        ImmutableList<TextualJMLConstruct> constructs;
        try {
            constructs = pp.parseClassLevel(text);
        } catch (RuntimeException e) {
            throw reportError(cls, "The generated JML clause %s does not parse: %s", text,
                e.getMessage());
        }
        services.addWarnings(pp.getWarnings());
        for (TextualJMLConstruct c : constructs) {
            if (c instanceof TextualJMLSpecCase) {
                throw reportError(cls,
                    "The generated JML clause %s was parsed as a specification case instead of "
                        + "a model declaration",
                    text);
            }
        }
        NodeList<JmlDoc> docs = new NodeList<>();
        docs.add(new JmlDoc(text));
        cls.addMember(new JmlDocDeclaration(docs));
    }
}
