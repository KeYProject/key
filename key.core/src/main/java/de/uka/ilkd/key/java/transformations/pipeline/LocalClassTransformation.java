/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.java.transformations.pipeline.lambda.NameGenerator;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Hoists local classes into unique {@code private static final} nested classes of the
 * enclosing type, making the captures of the local closure scope explicit.
 * <p>
 * JLS local classes may access variables of the creating context (effectively final
 * locals and parameters) and the enclosing instance. Since KeY reifies every class as a
 * nested class, this step
 * <ul>
 * <li>computes the captured local variables and parameters of the surrounding scope
 * (they become final fields {@code _outer_final_&lt;name&gt;} and constructor
 * parameters),</li>
 * <li>captures the enclosing instance if the body refers to it (fields
 * {@code outer_this} / {@code outer_super}),</li>
 * <li>moves the class declaration into the enclosing type as a unique
 * {@code private static final} class, and</li>
 * <li>rewrites the references in the bodies accordingly.</li>
 * </ul>
 * <p>
 * Local classes are hoisted innermost-first. A nested local class is moved into the
 * class that textually contains it; its outer-instance constructor argument is written
 * as {@code Owner.this}, which the hoisting of the outer class later turns into the
 * outer class' captured {@code outer_this} field. In this way closure chains of nested
 * lambdas are propagated without a special case (Csiky, Ch. 6.1: "nested lambda
 * expressions do not create a special case").
 * <p>
 * This is the second half of the lambda desugaring (Csiky Def. 3-5): the lambda replacer
 * emits lambdas as local classes, which are turned into the final nested classes here.
 * The step is written generically and works on any local class, in particular also on
 * user-written ones.
 *
 * @author engelc, weigl, csicar
 */
public class LocalClassTransformation extends JavaTransformerAbstract {

    /** Prefix for fields that hold captured variables (see {@link PipelineConstants}). */
    private static final String FINAL_VAR_PREFIX = PipelineConstants.FINAL_VAR_PREFIX;

    private static final String OUTER_THIS = "outer_this";
    private static final String OUTER_SUPER = "outer_super";

    public LocalClassTransformation(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        // A fresh generator per compilation unit guarantees unique names.
        NameGenerator names = new NameGenerator();
        boolean changed;
        do {
            changed = false;
            for (LocalClassDeclarationStmt stmt : cu.findAll(LocalClassDeclarationStmt.class)) {
                // Innermost first: only hoist a local class that does not itself contain
                // further local classes. They are hoisted first, so that at the moment of
                // the outer hoist, their instantiation arguments are plain expressions in
                // this class' body (and get rewritten together with the body).
                if (!stmt.getClassDeclaration()
                        .findAll(LocalClassDeclarationStmt.class).isEmpty()) {
                    continue;
                }
                if (!stmt.hasParentNode()) {
                    continue;
                }
                hoist(stmt, names);
                changed = true;
                // The collected list is stale after the first hoist; restart.
                break;
            }
        } while (changed);
    }

    private void hoist(LocalClassDeclarationStmt stmt, NameGenerator names) {
        ClassOrInterfaceDeclaration decl = stmt.getClassDeclaration();
        TypeDeclaration<?> enclosing = ancestorOf(decl).orElseThrow(
            () -> new IllegalStateException(
                "Local class '" + decl.getName() + "' without an enclosing type"));
        // Hoisted classes become members of a CLASS: Java does not permit private static
        // nested classes inside interfaces (their members are implicitly public), while
        // local classes may be declared inside interface methods.
        TypeDeclaration<?> hoistTarget = hoistTargetOf(enclosing);
        if (hoistTarget == null) {
            throw reportError(decl, "No enclosing class to hoist local class %s into",
                decl.getNameAsString());
        }

        // 1) Capture analysis -----------------------------------------------------
        // Local variables and parameters of the surrounding scope, in order of first
        // occurrence. The analysis includes the subtree of nested classes (which are
        // already hoisted as members), so that variables only referenced through a
        // nested instance creation argument are captured here as well.
        Map<String, Type> captured = new LinkedHashMap<>();
        boolean hasOuterThis = false;
        boolean hasOuterSuper = false;
        TypeDeclaration<?> outerOwner = null;

        for (NameExpr ne : decl.findAll(NameExpr.class)) {
            if (!insideDecl(ne, decl)) {
                continue;
            }
            ResolvedValueDeclaration resolved = resolve(ne);
            if (resolved == null) {
                continue;
            }
            if (resolved.isParameter()) {
                ResolvedParameterDeclaration p = resolved.asParameter();
                if (!isWithin(decl, p)) {
                    captured.putIfAbsent(p.getName(), astTypeOf(p, decl));
                }
            } else if (resolved.isVariable()) {
                Type capturedType = capturedVariableType(ne, resolved, decl);
                if (capturedType != null) {
                    captured.putIfAbsent(ne.getNameAsString(), capturedType);
                }
            } else if (resolved.isField()) {
                ResolvedFieldDeclaration fd = resolved.asField();
                if (fd.isStatic()) {
                    continue;
                }
                TypeDeclaration<?> owner = outerOwnerOf(fd.declaringType(), enclosing);
                if (owner != null) {
                    hasOuterThis = true;
                    outerOwner = mergeOwner(outerOwner, owner, decl);
                }
            }
        }
        for (MethodCallExpr mc : decl.findAll(MethodCallExpr.class)) {
            if (!insideDecl(mc, decl) || mc.getScope().isPresent()) {
                continue;
            }
            ResolvedMethodDeclaration m = resolve(mc);
            if (m == null || m.isStatic()) {
                continue;
            }
            TypeDeclaration<?> owner = outerOwnerOf(m.declaringType(), enclosing);
            if (owner != null) {
                hasOuterThis = true;
                outerOwner = mergeOwner(outerOwner, owner, decl);
            }
        }
        for (ThisExpr te : decl.findAll(ThisExpr.class)) {
            if (!insideDecl(te, decl) || te.getTypeName().isEmpty()) {
                continue;
            }
            hasOuterThis = true;
            TypeDeclaration<?> owner =
                ancestorNamed(enclosing, te.getTypeName().get().getIdentifier());
            if (owner == null) {
                owner = enclosing;
            }
            outerOwner = mergeOwner(outerOwner, owner, decl);
        }
        for (SuperExpr se : decl.findAll(SuperExpr.class)) {
            if (!insideDecl(se, decl) || se.getTypeName().isEmpty()) {
                continue;
            }
            hasOuterSuper = true;
            TypeDeclaration<?> owner =
                ancestorNamed(enclosing, se.getTypeName().get().getIdentifier());
            if (owner == null) {
                owner = enclosing;
            }
            outerOwner = mergeOwner(outerOwner, owner, decl);
        }

        // 2) Rewrite references in the moved bodies --------------------------------
        String outerThis = names.freshName(OUTER_THIS);
        String outerSuper = hasOuterSuper ? names.freshName(OUTER_SUPER) : null;
        for (BodyDeclaration<?> member : decl.getMembers()) {
            rewrite(member, decl, captured.keySet(), outerThis, outerSuper, false);
        }

        // 3) Fields and constructor ------------------------------------------------
        var ctorParams = new NodeList<Parameter>();
        var ctorAssignments = new NodeList<ExpressionStmt>();

        for (Map.Entry<String, Type> c : captured.entrySet()) {
            String fieldName = FINAL_VAR_PREFIX + c.getKey();
            decl.addMember(new FieldDeclaration(
                new NodeList<>(Modifier.privateModifier(), Modifier.finalModifier()),
                c.getValue(), fieldName));
            ctorParams.add(new Parameter(c.getValue(), c.getKey()));
            ctorAssignments.add(new ExpressionStmt(new AssignExpr(
                new FieldAccessExpr(new ThisExpr(), fieldName),
                new NameExpr(c.getKey()), AssignExpr.Operator.ASSIGN)));
        }
        if (outerOwner != null && (hasOuterThis || hasOuterSuper)) {
            Type enclosingType = services.getType(outerOwner);
            decl.addMember(new FieldDeclaration(
                new NodeList<>(Modifier.privateModifier(), Modifier.finalModifier()),
                enclosingType, outerThis));
            ctorParams.add(new Parameter(enclosingType, outerThis));
            ctorAssignments.add(new ExpressionStmt(new AssignExpr(
                new FieldAccessExpr(new ThisExpr(), outerThis),
                new NameExpr(outerThis), AssignExpr.Operator.ASSIGN)));
            if (hasOuterSuper) {
                decl.addMember(new FieldDeclaration(
                    new NodeList<>(Modifier.privateModifier(), Modifier.finalModifier()),
                    enclosingType, outerSuper));
                ctorParams.add(new Parameter(enclosingType, outerSuper));
                ctorAssignments.add(new ExpressionStmt(new AssignExpr(
                    new FieldAccessExpr(new ThisExpr(), outerSuper),
                    new NameExpr(outerSuper), AssignExpr.Operator.ASSIGN)));
            }
        }

        ConstructorDeclaration ctor = new ConstructorDeclaration(
            new NodeList<>(Modifier.publicModifier()), decl.getNameAsString());
        ctor.setParameters(ctorParams);
        BlockStmt ctorBody = ctor.getBody()
                .orElseGet(() -> {
                    BlockStmt b = new BlockStmt();
                    ctor.setBody(b);
                    return b;
                });
        ctorAssignments.forEach(ctorBody::addStatement);
        decl.addMember(ctor);

        // 4) Make the class a unique private static final nested class --------------
        String originalName = decl.getNameAsString();
        String hoistedName = originalName;
        final String candidateName = hoistedName;
        if (hoistTarget.getMembers().stream()
                .filter(m -> m instanceof TypeDeclaration<?>)
                .map(m -> ((TypeDeclaration<?>) m).getNameAsString())
                .anyMatch(name -> name.equals(candidateName))) {
            hoistedName = names.fresh(hoistedName);
        }
        decl.setName(hoistedName);
        decl.setModifiers(
            new NodeList<>(Modifier.privateModifier(), Modifier.staticModifier(),
                Modifier.finalModifier()));

        // 5) Update the instantiation sites ----------------------------------------
        // Argument order corresponds to the constructor parameter order.
        for (ObjectCreationExpr oce : hoistTarget.findAll(ObjectCreationExpr.class)) {
            boolean matches = oce.getType().isClassOrInterfaceType()
                    && originalName.equals(
                        oce.getType().asClassOrInterfaceType().getNameAsString());
            if (!matches) {
                continue;
            }
            oce.setType(hoistedName);
            var args = new NodeList<Expression>();
            captured.keySet().forEach(n -> args.add(new NameExpr(n)));
            if (outerOwner != null) {
                Expression outerArg = outerInstanceExpr(outerOwner, enclosing);
                args.add(outerArg.clone());
                if (hasOuterSuper) {
                    args.add(outerArg.clone());
                }
            }
            oce.setArguments(args);
        }

        // 6) Move the class into the enclosing type --------------------------------
        stmt.remove();
        hoistTarget.addMember(decl);
    }

    /**
     * The expression denoting the enclosing instance at the instantiation site: a bare
     * {@code this} if the instance is the immediate enclosing type itself, otherwise the
     * qualified form {@code Owner.this}. The qualified form is later rewritten to the
     * {@code outer_this} field of the enclosing hoisted class.
     */
    private Expression outerInstanceExpr(TypeDeclaration<?> owner, TypeDeclaration<?> enclosing) {
        if (owner == enclosing) {
            return new ThisExpr();
        }
        return new ThisExpr(new Name(owner.getNameAsString()));
    }

    // --------------------------------------------------------------------------------
    // Reference rewriting (Csiky Def. 5 "escapeKW")
    // --------------------------------------------------------------------------------

    private void rewrite(Node node, ClassOrInterfaceDeclaration decl, Set<String> captured,
            String outerThis, @Nullable String outerSuper, boolean inAnonymous) {
        if (node instanceof TypeDeclaration<?>) {
            // Nested classes have their own `this` and scope; they were hoisted
            // separately (innermost first).
            return;
        }
        if (node instanceof ObjectCreationExpr oce && oce.getAnonymousClassBody().isPresent()) {
            for (Expression arg : new ArrayList<>(oce.getArguments())) {
                rewrite(arg, decl, captured, outerThis, outerSuper, inAnonymous);
            }
            for (BodyDeclaration<?> member : new ArrayList<>(oce.getAnonymousClassBody().get())) {
                rewrite(member, decl, captured, outerThis, outerSuper, true);
            }
            return;
        }
        if (node instanceof NameExpr ne) {
            rewriteName(ne, decl, captured, outerThis);
        } else if (node instanceof MethodCallExpr mc && mc.getScope().isEmpty()) {
            ResolvedMethodDeclaration m = resolve(mc);
            if (m != null && !m.isStatic()
                    && outerOwnerOf(m.declaringType(), ancestorOf(decl).orElse(decl)) != null) {
                mc.setScope(new NameExpr(outerThis));
            }
        } else if (node instanceof ThisExpr te
                && te.getTypeName().isPresent() && !inAnonymous) {
            te.replace(new NameExpr(outerThis));
        } else if (node instanceof SuperExpr se
                && se.getTypeName().isPresent() && !inAnonymous && outerSuper != null) {
            se.replace(new NameExpr(outerSuper));
        }
        for (Node child : new ArrayList<>(node.getChildNodes())) {
            rewrite(child, decl, captured, outerThis, outerSuper, inAnonymous);
        }
    }

    private void rewriteName(NameExpr ne, ClassOrInterfaceDeclaration decl,
            Set<String> captured, String outerThis) {
        // References to the class' own fields and parameters resolve naturally within
        // the class and must not be rewritten.
        boolean shadowed = declaresField(decl, ne.getNameAsString())
                || isMethodParameter(ne, ne.getNameAsString());
        if (shadowed) {
            return;
        }
        if (captured.contains(ne.getNameAsString())) {
            ne.replace(new FieldAccessExpr(new ThisExpr(),
                FINAL_VAR_PREFIX + ne.getNameAsString()));
            return;
        }
        ResolvedValueDeclaration resolved = resolve(ne);
        if (resolved != null && resolved.isField()) {
            ResolvedFieldDeclaration fd = resolved.asField();
            if (!fd.isStatic()
                    && outerOwnerOf(fd.declaringType(), ancestorOf(decl).orElse(decl)) != null) {
                ne.replace(new FieldAccessExpr(new NameExpr(outerThis), ne.getNameAsString()));
            }
        }
    }

    private static boolean declaresField(ClassOrInterfaceDeclaration decl, String name) {
        return decl.getFields().stream()
                .flatMap(f -> f.getVariables().stream())
                .anyMatch(v -> v.getNameAsString().equals(name));
    }

    private static boolean isMethodParameter(NameExpr ne, String name) {
        return ne.findAncestor(MethodDeclaration.class)
                .map(m -> m.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(name)))
                .orElse(false);
    }

    // --------------------------------------------------------------------------------
    // Outer instance detection
    // --------------------------------------------------------------------------------

    /**
     * If {@code owner} is the declaring type of a member that is referenced from within
     * the hoisted class, it must be one of the physical enclosing types; the matching
     * {@link TypeDeclaration} is returned, or {@code null} if the member is declared
     * elsewhere (e.g. within the hoisted class itself or one of its sibling classes).
     */
    private @Nullable TypeDeclaration<?> outerOwnerOf(ResolvedTypeDeclaration owner,
            TypeDeclaration<?> enclosing) {
        for (TypeDeclaration<?> t = enclosing; t != null; t = ancestorOf(t).orElse(null)) {
            if (matches(t, owner)) {
                return t;
            }
        }
        return null;
    }

    private boolean matches(TypeDeclaration<?> t, ResolvedTypeDeclaration owner) {
        try {
            return t.resolve().getQualifiedName().equals(owner.getQualifiedName());
        } catch (RuntimeException e) {
            return t.getNameAsString().equals(owner.getName());
        }
    }

    private @Nullable TypeDeclaration<?> ancestorNamed(TypeDeclaration<?> enclosing,
            String name) {
        for (TypeDeclaration<?> t = enclosing; t != null; t = ancestorOf(t).orElse(null)) {
            if (t.getNameAsString().equals(name)) {
                return t;
            }
        }
        return null;
    }

    private @Nullable TypeDeclaration<?> mergeOwner(@Nullable TypeDeclaration<?> a,
            TypeDeclaration<?> b, Node where) {
        if (a == null || a == b) {
            return b;
        }
        for (TypeDeclaration<?> t = ancestorOf(a).orElse(null); t != null; t =
            ancestorOf(t).orElse(null)) {
            if (t == b) {
                return b; // b is an ancestor of a: the outermost instance
            }
        }
        for (TypeDeclaration<?> t = ancestorOf(b).orElse(null); t != null; t =
            ancestorOf(t).orElse(null)) {
            if (t == a) {
                return a; // a is an ancestor of b
            }
        }
        throw reportError(where,
            "Multiple distinct enclosing instances are required: %s and %s",
            a.getNameAsString(), b.getNameAsString());
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    private static Optional<TypeDeclaration<?>> ancestorOf(TypeDeclaration<?> t) {
        return (Optional) t.findAncestor(TypeDeclaration.class);
    }

    /**
     * The nearest enclosing class (skipping interfaces) of {@code enclosing}, walking up
     * the type-declaration chain. See the comment in {@link #hoist}.
     */
    private static @Nullable TypeDeclaration<?> hoistTargetOf(TypeDeclaration<?> enclosing) {
        for (TypeDeclaration<?> t = enclosing; t != null; t = ancestorOf(t).orElse(null)) {
            if (t.isClassOrInterfaceDeclaration()
                    && !t.asClassOrInterfaceDeclaration().isInterface()) {
                return t;
            }
        }
        return null;
    }

    // --------------------------------------------------------------------------------
    // Helpers
    // --------------------------------------------------------------------------------

    private @Nullable ResolvedValueDeclaration resolve(NameExpr ne) {
        try {
            return ne.resolve();
        } catch (RuntimeException e) {
            return null;
        }
    }

    private @Nullable ResolvedMethodDeclaration resolve(MethodCallExpr mc) {
        try {
            return mc.resolve();
        } catch (RuntimeException e) {
            return null;
        }
    }

    /** Is the declaration of {@code resolved} part of the subtree of {@code decl}? */
    private boolean isWithin(TypeDeclaration<?> decl, ResolvedValueDeclaration resolved) {
        return resolved.toAst().map(ast -> isWithin(decl, ast)).orElse(false);
    }

    /** Is the AST location {@code node} part of the subtree of {@code decl}? */
    private boolean isWithin(TypeDeclaration<?> decl, Node node) {
        Node cur = node;
        while (cur != null) {
            if (cur == decl) {
                return true;
            }
            cur = cur.getParentNode().orElse(null);
        }
        return false;
    }

    /**
     * Is {@code node} directly contained in the body of {@code decl} (rather than in one
     * of its nested type declarations)? Nested member classes have their own {@code this}
     * and closure scope: references like {@code A.this.f} inside a member class of the
     * hoisted class resolve through the inner-class instance chain and remain valid after
     * the class is hoisted, so they must not count as captures of the outer instance.
     */
    private boolean insideDecl(Node node, ClassOrInterfaceDeclaration decl) {
        Node cur = node;
        while (cur != null) {
            if (cur instanceof TypeDeclaration) {
                return cur == decl;
            }
            cur = cur.getParentNode().orElse(null);
        }
        return false;
    }

    /**
     * The type used for the capture of a local variable, or {@code null} if the variable
     * is declared inside the class itself. The solver maps locals back to the enclosing
     * {@link VariableDeclarationExpr} (which contains the {@link VariableDeclarator}), so
     * both node kinds are considered; when the mapping fails, the resolved type is used.
     */
    private @Nullable Type capturedVariableType(NameExpr ne, ResolvedValueDeclaration resolved,
            ClassOrInterfaceDeclaration decl) {
        VariableDeclarator vd = variableDeclaratorOf(ne, resolved);
        if (vd != null) {
            if (isWithin(decl, vd)) {
                return null;
            }
            return erasedTypeVars(vd.getType().clone(), decl);
        }
        try {
            Type t = services.getType(resolved.getType());
            return t == null ? null : erasedTypeVars(t, decl);
        } catch (RuntimeException e) {
            return null;
        }
    }

    private @Nullable VariableDeclarator variableDeclaratorOf(NameExpr ne,
            ResolvedValueDeclaration resolved) {
        Optional<? extends Node> ast = resolved.toAst();
        if (ast.isEmpty()) {
            return null;
        }
        Node n = ast.get();
        if (n instanceof VariableDeclarator vd) {
            return vd;
        }
        if (n instanceof VariableDeclarationExpr vde) {
            for (VariableDeclarator vd : vde.getVariables()) {
                if (vd.getNameAsString().equals(ne.getNameAsString())) {
                    return vd;
                }
            }
        }
        return null;
    }

    /** JavaParser type syntax of a captured parameter (from its AST declaration). */
    private Type astTypeOf(ResolvedParameterDeclaration p, TypeDeclaration<?> decl) {
        Optional<? extends Node> ast = p.toAst();
        if (ast.isPresent() && ast.get() instanceof Parameter par) {
            return erasedTypeVars(par.getType().clone(), decl);
        }
        String describe = p.describeType();
        int idx = describe.indexOf('<');
        if (idx >= 0) {
            describe = describe.substring(0, idx);
        }
        return services.getType(describe.split("[.]"));
    }

    /**
     * Replaces type variables in {@code t} that are declared by an enclosing type with
     * {@code Object}, since the hoisted (static) class cannot refer to type parameters
     * of its enclosing types. A parameterized type whose arguments contain such a type
     * variable is erased to the raw type (JLS &sect;4.6).
     */
    private Type erasedTypeVars(Type t, TypeDeclaration<?> decl) {
        Set<String> vars = new LinkedHashSet<>();
        for (TypeDeclaration<?> cur = decl; cur != null; cur = ancestorOf(cur).orElse(null)) {
            if (cur instanceof NodeWithTypeParameters<?> tp) {
                tp.getTypeParameters().forEach(tp2 -> vars.add(tp2.getNameAsString()));
            }
        }
        if (vars.isEmpty()) {
            return t;
        }
        if (t.isClassOrInterfaceType()
                && vars.contains(t.asClassOrInterfaceType().getNameAsString())) {
            return new ClassOrInterfaceType(null, "Object");
        }
        List<ClassOrInterfaceType> uses = new ArrayList<>();
        t.walk(n -> {
            if (n instanceof ClassOrInterfaceType c
                    && vars.contains(c.getNameAsString())) {
                uses.add(c);
            }
        });
        if (uses.isEmpty()) {
            return t;
        }
        uses.forEach(c -> c.replace(new ClassOrInterfaceType(null, "Object")));
        if (t.isClassOrInterfaceType()) {
            t.asClassOrInterfaceType().removeTypeArguments();
        }
        return t;
    }
}
