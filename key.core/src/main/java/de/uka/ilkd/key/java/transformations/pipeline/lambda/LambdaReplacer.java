/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.transformations.pipeline.JavaTransformerAbstract;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.TypeExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedLambdaConstraintType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Replaces all lambda expressions and method references of a compilation unit by
 * local class declarations together with instance creation expressions.
 * <p>
 * A lambda expression {@code (a1, ..., an) -> body} is desugared into a local class
 * declaration
 * <pre>
 * final class FI__N implements FI {
 *     public T sam(A1 a1, ..., An an) {
 *         [return] body [;]
 *     }
 * }
 * new FI__N()
 * </pre>
 * immediately preceding the statement that contains the lambda expression. The local
 * class captures the surrounding scope implicitly (JLS local class semantics). It is
 * hoisted in a later pipeline step ({@link
 * de.uka.ilkd.key.java.transformations.pipeline.LocalClassTransformation}) into a
 * unique {@code private static final} nested class that captures the local closure
 * scope explicitly.
 * <p>
 * Inside the moved body, {@code this} and {@code super} are qualified with the
 * enclosing type name ({@code Outer.this} / {@code Outer.super}), because in a lambda
 * expression those keywords refer to the enclosing instance, while in the generated
 * class they would refer to the generated class itself (Csiky, Def. 5,
 * "escapeKW"). The hoisting step turns these qualified references into
 * {@code outer_this} / {@code outer_super} fields.
 * <p>
 * Method references are first normalized into equivalent lambda expressions
 * (Csiky, Ch. 6.2.4) which are then desugared like any other lambda. Nested lambdas
 * are desugared innermost-first, so that desugaring of a body never has to deal with
 * lambdas (Csiky, Def. 4).
 * <p>
 * This step reports a loud error (instead of silently miscompiling) when the target
 * functional interface of a lambda cannot be resolved, and when a lambda appears in a
 * context without an enclosing block statement, such as a field initializer (which
 * would require direct nested-class emission; not supported yet).
 *
 * @author weigl, csicar
 */
public class LambdaReplacer extends JavaTransformerAbstract {

    public LambdaReplacer(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        // A fresh generator per compilation unit guarantees unique names.
        NameGenerator names = new NameGenerator();

        // 1) Normalize all method references to lambdas (also those inside lambda bodies).
        for (MethodReferenceExpr mr : cu.findAll(MethodReferenceExpr.class)) {
            LambdaExpr lambda = normalizeMethodReference(mr, names);
            mr.replace(lambda);
        }

        // 2) Desugar all lambdas, innermost first (desugarLambda recurses into bodies).
        for (LambdaExpr lambda : cu.findAll(LambdaExpr.class)) {
            if (lambda.hasParentNode()) {
                desugarLambda(lambda, names);
            }
        }

        // 3) Guard: neither lambdas nor method references may remain, as the
        // downstream JP2KeYConverter rejects both.
        if (!cu.findAll(LambdaExpr.class).isEmpty()
                || !cu.findAll(MethodReferenceExpr.class).isEmpty()) {
            throw reportError(cu,
                "Lambda desugaring is incomplete: lambdas/method references remain");
        }
    }

    // --------------------------------------------------------------------------------
    // Lambda desugaring
    // --------------------------------------------------------------------------------

    private void desugarLambda(LambdaExpr lambda, NameGenerator names) {
        if (!lambda.hasParentNode()) {
            return;
        }
        TypeDeclaration<?> enclosing = enclosingTypeOf(lambda);

        // Nested lambdas are desugared first (Def. 4 of the thesis).
        for (LambdaExpr inner : lambda.getBody().findAll(LambdaExpr.class)) {
            if (inner.hasParentNode()) {
                desugarLambda(inner, names);
            }
        }

        ResolvedReferenceType fi = functionalInterfaceOf(lambda);
        ResolvedMethodDeclaration sam = samOf(fi, lambda);

        String fiName = fi.getTypeDeclaration().map(ResolvedReferenceTypeDeclaration::getName)
                .orElse("Func");
        String className = names.fresh(fiName);

        MethodDeclaration samMethod = samAsMethod(sam, fi, lambda);
        // The lambda parameters bind (positionally) to the SAM parameters.
        bindLambdaParameters(samMethod, lambda);
        samMethod.setBody(lambdaBody(lambda, sam));

        // Escape `this`/`super` so they keep referring to the enclosing instance.
        escapeThisSuper(samMethod, enclosing);

        ClassOrInterfaceDeclaration local = new ClassOrInterfaceDeclaration(
            new NodeList<>(Modifier.finalModifier()), false, className);
        local.setImplementedTypes(NodeList.nodeList(fiTypeSyntax(fi, lambda)));
        local.addMember(samMethod);

        ObjectCreationExpr creation = new ObjectCreationExpr();
        creation.setType(className);

        lambda.replace(creation);
        insertLocalClassDeclaration(local, creation);
    }

    private BlockStmt lambdaBody(LambdaExpr lambda, ResolvedMethodDeclaration sam) {
        var exprBody = lambda.getExpressionBody();
        if (exprBody.isPresent()) {
            Expression expr = exprBody.get().clone();
            BlockStmt block = new BlockStmt();
            if (sam.getReturnType().isVoid()) {
                block.addStatement(new ExpressionStmt(expr));
            } else {
                block.addStatement(new ReturnStmt(expr));
            }
            return block;
        }
        return lambda.getBody().asBlockStmt().clone();
    }

    /**
     * Names of the lambda parameters are bound to the SAM method parameters; types are
     * taken from the resolved SAM signature.
     */
    private void bindLambdaParameters(MethodDeclaration samMethod, LambdaExpr lambda) {
        var samParams = samMethod.getParameters();
        var lambdaParams = lambda.getParameters();
        for (int i = 0; i < Math.min(samParams.size(), lambdaParams.size()); i++) {
            samParams.get(i).setName(lambdaParams.get(i).getName());
        }
    }

    // --------------------------------------------------------------------------------
    // Method references (Csiky 6.2.4)
    // --------------------------------------------------------------------------------

    private LambdaExpr normalizeMethodReference(MethodReferenceExpr mr, NameGenerator names) {
        ResolvedReferenceType fi = functionalInterfaceOf(mr);
        ResolvedMethodDeclaration sam = samOf(fi, mr);
        Expression scope = mr.getScope();

        List<Parameter> params = new ArrayList<>();
        final Expression body;

        if ("new".equals(mr.getIdentifier())) {
            // Constructor reference T::new — parameters are given by the SAM.
            if (!(scope instanceof TypeExpr texpr)) {
                throw reportError(mr, "Unsupported constructor reference scope");
            }
            for (int i = 0; i < sam.getNumberOfParams(); i++) {
                params.add(new Parameter(typeOf(sam.getParam(i).getType(), fi, mr), "p" + i));
            }
            ObjectCreationExpr creation = new ObjectCreationExpr();
            if (!texpr.getType().isClassOrInterfaceType()) {
                throw reportError(mr, "Unsupported constructor reference type %s",
                    texpr.getType());
            }
            creation.setType(texpr.getType().asClassOrInterfaceType().clone());
            params.forEach(p -> creation.addArgument(new NameExpr(p.getNameAsString())));
            body = creation;
        } else {
            ResolvedMethodDeclaration method = mr.resolve();
            boolean isStatic = method.isStatic();
            if (scope instanceof TypeExpr texpr && resolvesAsType(texpr)) {
                // T::m — static method of T, or unbound instance method.
                if (isStatic) {
                    for (int i = 0; i < method.getNumberOfParams(); i++) {
                        params.add(
                            new Parameter(typeOf(method.getParam(i).getType(), fi, mr), "p" + i));
                    }
                    MethodCallExpr call = new MethodCallExpr(texpr.clone(), mr.getIdentifier());
                    params.forEach(p -> call.addArgument(new NameExpr(p.getNameAsString())));
                    body = call;
                } else {
                    // Unbound instance method: the first lambda parameter is the receiver.
                    params.add(new Parameter(texpr.getType().clone(), "p0"));
                    var methodParams = new ArrayList<Parameter>();
                    for (int i = 0; i < method.getNumberOfParams(); i++) {
                        var p =
                            new Parameter(typeOf(method.getParam(i).getType(), fi, mr),
                                "p" + (i + 1));
                        params.add(p);
                        methodParams.add(p);
                    }
                    MethodCallExpr call = new MethodCallExpr(new NameExpr("p0"),
                        mr.getIdentifier());
                    methodParams.forEach(p -> call.addArgument(new NameExpr(p.getNameAsString())));
                    body = call;
                }
            } else {
                // Bound instance method: expr::m or this::m. The JavaParser fork lexes a
                // simple-name receiver such as `s::isEmpty` as a TypeExpr; when that "type"
                // does not resolve (it is a local variable), the receiver is the expression
                // and is captured like any other escaped value.
                Expression receiver = scope instanceof TypeExpr texpr
                        ? new NameExpr(texpr.getType().asString())
                        : scope.clone();
                for (int i = 0; i < method.getNumberOfParams(); i++) {
                    params.add(
                        new Parameter(typeOf(method.getParam(i).getType(), fi, mr), "p" + i));
                }
                MethodCallExpr call = new MethodCallExpr(receiver, mr.getIdentifier());
                params.forEach(p -> call.addArgument(new NameExpr(p.getNameAsString())));
                body = call;
            }
        }
        return new LambdaExpr(new NodeList<>(params), new ExpressionStmt(body), false);
    }

    /**
     * Does the type expression name a real type in scope? A receiver that the fork lexed as
     * a type (e.g. the local variable {@code s} of {@code s::isEmpty}) fails to resolve.
     */
    private boolean resolvesAsType(TypeExpr texpr) {
        try {
            texpr.getType().resolve();
            return true;
        } catch (RuntimeException e) {
            return false;
        }
    }


    // --------------------------------------------------------------------------------
    // Resolution helpers
    // --------------------------------------------------------------------------------

    /**
     * The resolved functional interface type of a lambda expression or method reference.
     * If the symbol solver cannot infer the target type from the position (e.g. for
     * lambdas in return statements, which the fork's engine does not support), the
     * target type is recovered from the surrounding context instead.
     */
    private ResolvedReferenceType functionalInterfaceOf(Expression e) {
        return unwrapToFunctionalInterface(resolveTargetOrHintType(e, 0), e);
    }

    private ResolvedType resolveTargetOrHintType(Expression e, int depth) {
        try {
            return e.calculateResolvedType();
        } catch (RuntimeException ex) {
            if (depth > 8) {
                throw reportError(e, "Cannot resolve the target type of %s (%s)",
                    e, ex.getMessage());
            }
            ResolvedType hint = hintTypeFromContext(e, depth);
            if (hint != null) {
                return hint;
            }
            throw reportError(e, "Cannot resolve the target type of %s (%s)",
                e, ex.getMessage());
        }
    }

    private ResolvedReferenceType unwrapToFunctionalInterface(ResolvedType rt, Expression e) {
        if (rt.isConstraint() && rt instanceof ResolvedLambdaConstraintType v) {
            rt = v.getBound();
        }
        if (!rt.isReferenceType()) {
            throw reportError(e, "Target type of %s is not a functional interface: %s",
                e, rt.describe());
        }
        return rt.asReferenceType();
    }

    /**
     * Recovers the target type of a lambda or method reference from its syntactic
     * context: variable declarator, assignment target, cast, enclosing method or lambda
     * return type, argument of a method/constructor call, or enclosing conditional.
     */
    private @Nullable ResolvedType hintTypeFromContext(Expression e, int depth) {
        Node cur = e.getParentNode().orElse(null);
        while (cur != null) {
            if (cur instanceof VariableDeclarator vd) {
                if (vd.getType().isVarType()) {
                    return null;
                }
                return tryResolve(() -> vd.resolve().getType());
            }
            if (cur instanceof AssignExpr ae && ae.getValue() == e) {
                ResolvedType t = tryResolve(ae.getTarget()::calculateResolvedType);
                if (t != null) {
                    return t;
                }
            }
            if (cur instanceof CastExpr ce && ce.getExpression() == e) {
                return tryResolve(ce.getType()::resolve);
            }
            if (cur instanceof ReturnStmt rs && rs.getExpression().orElse(null) == e) {
                return returnTargetType(rs, depth);
            }
            if (cur instanceof MethodCallExpr mc) {
                int idx = mc.getArguments().indexOf(e);
                if (idx >= 0) {
                    ResolvedType t = tryResolve(() -> mc.resolve().getParam(idx).getType());
                    if (t != null) {
                        return t;
                    }
                }
            }
            if (cur instanceof ObjectCreationExpr oce) {
                int idx = oce.getArguments().indexOf(e);
                if (idx >= 0) {
                    ResolvedType t = tryResolve(() -> oce.resolve().getParam(idx).getType());
                    if (t != null) {
                        return t;
                    }
                }
            }
            if (cur instanceof ConditionalExpr ce
                    && (ce.getThenExpr() == e || ce.getElseExpr() == e)) {
                return hintTypeFromContext(ce, depth);
            }
            cur = cur.getParentNode().orElse(null);
        }
        return null;
    }

    /**
     * The declared return type of the method (or enclosing lambda) that the return
     * statement {@code rs} belongs to. Nested type declarations terminate the walk.
     */
    private @Nullable ResolvedType returnTargetType(ReturnStmt rs, int depth) {
        Node anc = rs;
        while (anc != null) {
            anc = anc.getParentNode().orElse(null);
            if (anc instanceof LambdaExpr outer) {
                ResolvedType ft = resolveTargetOrHintType(outer, depth + 1);
                if (!ft.isReferenceType()) {
                    return null;
                }
                ResolvedMethodDeclaration sam = samOfOrNull(ft.asReferenceType(), outer);
                return sam == null ? null : sam.getReturnType();
            }
            if (anc instanceof MethodDeclaration md) {
                return tryResolve(() -> md.resolve().getReturnType());
            }
            if (anc instanceof TypeDeclaration<?>) {
                // a local or member class terminates the enclosing-instance walk
                return null;
            }
            if (anc instanceof ObjectCreationExpr oce && oce.getAnonymousClassBody().isPresent()) {
                return null;
            }
            if (anc instanceof InitializerDeclaration) {
                return null;
            }
        }
        return null;
    }

    private @Nullable ResolvedType tryResolve(java.util.function.Supplier<ResolvedType> s) {
        try {
            return s.get();
        } catch (RuntimeException e) {
            return null;
        }
    }

    /**
     * The single abstract method of the functional interface (JLS &sect;9.8), also
     * considering inherited methods (default and abstract methods are excluded).
     */
    private ResolvedMethodDeclaration samOf(ResolvedReferenceType fi, Node where) {
        ResolvedReferenceTypeDeclaration tid =
            fi.getTypeDeclaration().orElseThrow(
                () -> reportError(where, "Cannot resolve the functional interface %s",
                    fi.describe()));
        List<ResolvedMethodDeclaration> candidates = new ArrayList<>();
        for (ResolvedMethodDeclaration m : fi.getAllMethods()) {
            if (!m.isAbstract() || m.isDefaultMethod() || m.isStatic()) {
                continue;
            }
            if ("java.lang.Object".equals(m.declaringType().getQualifiedName())
                    || m.getQualifiedSignature().startsWith("java.lang.Object.")) {
                continue;
            }
            candidates.add(m);
        }
        if (candidates.size() != 1) {
            throw reportError(where, "%s is not a functional interface: found %d abstract methods",
                fi.describe(), candidates.size());
        }
        return candidates.get(0);
    }

    private @Nullable ResolvedMethodDeclaration samOfOrNull(ResolvedReferenceType fi,
            Node where) {
        try {
            return samOf(fi, where);
        } catch (RuntimeException e) {
            return null;
        }
    }

    /**
     * Reifies a resolved type into JavaParser type syntax, substituting type variables
     * with the type arguments of the functional interface.
     */
    private Type typeOf(ResolvedType t, ResolvedReferenceType fi, Node where) {
        ResolvedTypeParametersMap params = fi.typeParametersMap();
        if (t.isTypeVariable()) {
            ResolvedType mapped = params.getValue(t.asTypeParameter());
            if (mapped != null) {
                t = mapped;
            }
        }
        if (t.isTypeVariable() || t.isWildcard()) {
            t = t.erasure();
        }
        if (t.isVoid()) {
            return new VoidType();
        }
        Type syntax = services.getType(t);
        if (syntax == null) {
            throw reportError(where, "Cannot reify resolved type %s", t.describe());
        }
        return syntax;
    }

    private MethodDeclaration samAsMethod(ResolvedMethodDeclaration sam,
            ResolvedReferenceType fi, Node where) {
        MethodDeclaration m = new MethodDeclaration();
        m.setType(typeOf(sam.getReturnType(), fi, where));
        m.setName(sam.getName());
        m.setModifiers(NodeList.nodeList(Modifier.publicModifier()));
        for (int i = 0; i < sam.getNumberOfParams(); i++) {
            ResolvedParameterDeclaration p = sam.getParam(i);
            m.addParameter(typeOf(p.getType(), fi, where), p.getName());
        }
        return m;
    }

    /**
     * JavaParser type syntax of the functional interface including type arguments,
     * e.g. {@code MyFunctionalInterface<Integer>}.
     */
    private ClassOrInterfaceType fiTypeSyntax(ResolvedReferenceType fi, Node where) {
        ClassOrInterfaceType t = services.getType(fi.getQualifiedName().split("[.]"));
        var typeArgs = new NodeList<Type>();
        for (var pair : fi.getTypeParametersMap()) {
            ResolvedType arg = pair.b;
            if (!arg.isReferenceType() || arg.isTypeVariable() || arg.describe().contains("<")) {
                // Only simple reference type arguments are supported; otherwise the raw
                // type is used, which is unproblematic for the subsequent desugaring.
                continue;
            }
            typeArgs.add(new ClassOrInterfaceType(null, arg.describe()));
        }
        if (!typeArgs.isEmpty()) {
            t.setTypeArguments(typeArgs);
        }
        return t;
    }

    // --------------------------------------------------------------------------------
    // Context handling
    // --------------------------------------------------------------------------------

    private void insertLocalClassDeclaration(ClassOrInterfaceDeclaration local,
            ObjectCreationExpr creation) {
        // Find the enclosing statement that is a direct child of a block statement.
        Node cur = creation;
        while (cur != null) {
            var parent = cur.getParentNode();
            if (parent.isPresent() && parent.get() instanceof BlockStmt block
                    && cur instanceof Statement stmt) {
                block.getStatements().add(block.getStatements().indexOf(stmt),
                    new LocalClassDeclarationStmt(local));
                return;
            }
            cur = parent.orElse(null);
        }
        throw reportError(creation, "Lambda in a context without an enclosing statement is not "
            + "supported yet (e.g. field initializer)");
    }

    private TypeDeclaration<?> enclosingTypeOf(Expression e) {
        TypeDeclaration<?> enclosing = e.findAncestor(TypeDeclaration.class).orElseThrow(
            () -> reportError(e, "Lambda expression without enclosing type declaration"));
        if (enclosing instanceof ClassOrInterfaceDeclaration cid
                && cid.getParentNode().isPresent()
                && cid.getParentNode().get() instanceof ObjectCreationExpr) {
            throw reportError(e,
                "Lambdas inside anonymous classes are not supported yet (enclosing type %s)",
                cid.getName());
        }
        return enclosing;
    }

    // --------------------------------------------------------------------------------
    // Escaping `this` / `super` (Csiky Def. 5, restricted to the qualification)
    // --------------------------------------------------------------------------------

    /**
     * Qualifies all unqualified {@code this} / {@code super} references below {@code node}
     * with the name of {@code enclosing}. Does not descend into nested type declarations
     * or anonymous class bodies, which introduce their own {@code this} / {@code super}.
     */
    private void escapeThisSuper(Node node, TypeDeclaration<?> enclosing) {
        if (node instanceof TypeDeclaration<?> || node instanceof LocalClassDeclarationStmt) {
            return;
        }
        if (node instanceof ObjectCreationExpr oce && oce.getAnonymousClassBody().isPresent()) {
            // Do not enter the anonymous class body; only its arguments belong to the
            // enclosing context.
            for (Expression arg : oce.getArguments()) {
                escapeThisSuper(arg, enclosing);
            }
            return;
        }
        if (node instanceof ThisExpr te && te.getTypeName().isEmpty()) {
            te.setTypeName(new Name(enclosing.getNameAsString()));
        } else if (node instanceof SuperExpr se && se.getTypeName().isEmpty()) {
            se.setTypeName(new Name(enclosing.getNameAsString()));
        }
        for (Node child : node.getChildNodes()) {
            escapeThisSuper(child, enclosing);
        }
    }
}
