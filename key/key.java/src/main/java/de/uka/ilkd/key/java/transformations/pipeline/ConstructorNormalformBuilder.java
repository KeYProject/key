// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;

import java.util.Optional;
import java.util.stream.Collectors;

import static de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER;
import static de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices.cloneList;

/**
 * Transforms the constructors of the given class to their
 * normalform. The constructor normalform can then be accessed via a
 * methodcall <code>&lt;init&gt;<cons_args)</code>. The visibility of
 * the normalform is the same as for the original constructor.
 */
public class ConstructorNormalformBuilder extends JavaTransformer {
    /**
     * creates the constructor normalform builder
     */
    public ConstructorNormalformBuilder(TransformationPipelineServices services) {
        super(services);
    }

    protected Optional<FieldDeclaration> getImplicitEnclosingThis(TypeDeclaration<?> cd) {
        return cd.getFieldByName(PipelineConstants.IMPLICIT_ENCLOSING_THIS);
    }

    private void attachDefaultConstructor(ClassOrInterfaceDeclaration cd) {
        var body = new BlockStmt();
        body.addStatement(new MethodCallExpr(new SuperExpr(), CONSTRUCTOR_NORMALFORM_IDENTIFIER));
        var initializers = services.getInitializers(cd);
        int i = 0;
        for (Statement initializer : initializers) {
            body.addStatement(i++, initializer.clone());
        }
        MethodDeclaration def = cd.addMethod(CONSTRUCTOR_NORMALFORM_IDENTIFIER, Modifier.Keyword.PUBLIC);
        def.setBody(body);
    }

    /**
     * Creates the normalform of the given constructor, that is declared
     * in class cd. For a detailed description of the normalform to be
     * built see the KeY Manual.
     *
     * @param cd   the TypeDeclaration<?> where the cons is declared
     * @param cons the Constructor to be transformed
     */
    private void normalform(ClassOrInterfaceDeclaration cd, ConstructorDeclaration cons) {
        NodeList<Modifier> mods = new NodeList<>();
        var et = getImplicitEnclosingThis(cd);
        var td = getEnclosingClass(cd).get();
        var outerVars = services.getFinalVariables(cd);
        int j = !et.isPresent() ? 0 : 1;
        if (outerVars != null) j += outerVars.size();
        Parameter pd = null;
        AssignExpr ca = null;
        String etId = "_ENCLOSING_THIS";
        if (et.isPresent()) {
            pd = new Parameter(
                    new ClassOrInterfaceType(null, td.getName().getIdentifier()),
                    etId);
            ca = new AssignExpr(
                    new FieldAccessExpr(new ThisExpr(), et.get().getVariables().get(0).getName().getIdentifier()),
                    new NameExpr(etId), AssignExpr.Operator.ASSIGN);
        }

        BlockStmt body;
        NodeList<ReferenceType> recThrows;
        NodeList<Parameter> parameters;
        if (!(cons instanceof ConstructorDeclaration)) {
            mods.add(new Modifier(Modifier.Keyword.PUBLIC));
            parameters = new NodeList<>();
            recThrows = null;
            body = new BlockStmt();
        } else {
            mods = cloneList(cons.getModifiers());
            parameters = cloneList(cons.getParameters());
            recThrows = cloneList(cons.getThrownExceptions());

            BlockStmt origBody = cons.getBody();
            if (origBody == null) // may happen if a stub is defined with an empty constructor
                body = null;
            else
                body = origBody.clone();
        }

        if (outerVars != null && !outerVars.isEmpty()) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }

            for (var v : outerVars) {
                parameters.add(new Parameter(services.getType(v.getType()), v.getName()));
            }
        }

        if (pd != null) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }
            parameters.add(pd);
        }

        if (cd.resolve().isJavaLangObject() && body != null) {
            // remember original first statement
            Statement first = !body.getStatements().isEmpty() ? body.getStatement(0) : null;

            // first statement has to be a this or super constructor call
            if (!(first instanceof ExplicitConstructorInvocationStmt)) {
                body.addStatement(0, new MethodCallExpr(new SuperExpr(), CONSTRUCTOR_NORMALFORM_IDENTIFIER));
            } else {
                body.getStatements().remove(0);
                var constructorCall = (ExplicitConstructorInvocationStmt) first;
                if (constructorCall.isThis()) {
                    var methodCall = new MethodCallExpr(new ThisExpr(),
                            constructorCall.getTypeArguments().orElse(null), //copy?
                            CONSTRUCTOR_NORMALFORM_IDENTIFIER,
                            constructorCall.getArguments() /*copy?*/);
                    body.addStatement(0, methodCall);
                } else {
                    NodeList<Expression> args = constructorCall.getArguments();
                    if (constructorCall.getExpression().isPresent()) {
                        if (args == null) args = new NodeList<>();
                        args.add((constructorCall.getExpression().get()));
                    } else if (!cd.resolve().getAllAncestors().isEmpty()) {
                        if (args == null) args = new NodeList<>();
                        args.add(new NameExpr(etId));
                    }
                    var expr = new MethodCallExpr(new SuperExpr(),
                            null,
                            CONSTRUCTOR_NORMALFORM_IDENTIFIER,
                            args);
                    body.addStatement(0, expr);
                }
            }

            // if the first statement is not a this constructor reference
            // the instance initializers have to be added in source code
            // order
            if (!(first instanceof ExplicitConstructorInvocationStmt)) {
                NodeList<Statement> initializers = services.getInitializers(cd);
                if (ca != null) {
                    body.addStatement(0, ca);
                }

                int i = 0;
                for (ResolvedFieldDeclaration outerVar : outerVars) {
                    final var fieldAccessExpr = new FieldAccessExpr(new ThisExpr(),
                            PipelineConstants.FINAL_VAR_PREFIX + outerVar.getName());
                    var assign = new AssignExpr(fieldAccessExpr, new NameExpr(outerVar.getName()),
                            AssignExpr.Operator.ASSIGN);
                    body.addStatement((ca != null ? 1 : 0) + (i++), assign);
                }

                for (i = 0; i < initializers.size(); i++) {
                    body.addStatement(i + j + 1, initializers.get(i).clone());
                }
            }
        }

        MethodDeclaration nf = new MethodDeclaration(
                mods,
                new VoidType(),
                CONSTRUCTOR_NORMALFORM_IDENTIFIER);
        nf.setParameters(parameters);
        nf.setThrownExceptions(recThrows);
        nf.setBody(body);
        cd.addMember(nf);
    }

    private Optional<ClassOrInterfaceDeclaration> getEnclosingClass(ClassOrInterfaceDeclaration cd) {
        if (cd.isNestedType()) {
            return cd.getParentNode().map(ClassOrInterfaceDeclaration.class::cast);
        }
        return Optional.empty();
    }

    private ConstructorDeclaration attachConstructorDecl(TypeDeclaration<?> td) {
        if (td.getParentNode().get() instanceof ObjectCreationExpr) {
            var n = (ObjectCreationExpr) td.getParentNode().get();
            final var args = n.getArguments();
            if (args == null || args.size() == 0) return null;

            var type = n.getType().resolve();
            var constr = n.resolve().toAst().get();
            constr = constr.clone();
            final NodeList<Expression> cargs = new NodeList<>(args.stream().map(Expression::clone).collect(Collectors.toList()));
            var sr = new MethodCallExpr(null, new NodeList<>(), new SimpleName("super"), cargs);
            constr.setBody(new BlockStmt(new NodeList<>(new ExpressionStmt(sr))));
            td.addMember(constr);
            return constr;
        }
        return null;
    }

    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    public void apply(TypeDeclaration<?> td) {
        if (td instanceof ClassOrInterfaceDeclaration) {
            var cd = (ClassOrInterfaceDeclaration) td;
            var constructors = td.getConstructors();
            ConstructorDeclaration anonConstr = null;
            if (cd.getName() == null) {
                anonConstr = attachConstructorDecl(td);
            }
            if (anonConstr != null) constructors.add(anonConstr);
            for (ConstructorDeclaration constructor : constructors) {
                normalform(cd, constructor);
            }

            var mdl = td.getMethods();
            for (MethodDeclaration md : mdl) {
                cd.addMember(md);
            }
        }
    }
}