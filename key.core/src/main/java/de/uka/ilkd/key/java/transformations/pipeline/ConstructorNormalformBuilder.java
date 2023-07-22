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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import de.uka.ilkd.key.java.loader.JavaParserFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Optional;
import java.util.stream.Collectors;

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
        body.addStatement(new MethodCallExpr(new SuperExpr(),
                PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER));
        var initializers = services.getInitializers(cd);
        int i = 0;
        for (Statement initializer : initializers) {
            body.addStatement(i++, initializer.clone());
        }
        MethodDeclaration def =
                cd.addMethod(PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER,
                        Modifier.Keyword.PUBLIC);
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
    private void normalform(@Nonnull ClassOrInterfaceDeclaration cd, @Nonnull ConstructorDeclaration cons) {
        final var enclosingClass = getEnclosingClass(cd);
        NodeList<Modifier> mods = new NodeList<>();

        MethodDeclaration nf = new MethodDeclaration(
                mods,
                new VoidType(),
                PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER);
        final NodeList<Parameter> parameters = new NodeList<>();
        nf.setParameters(parameters);
        final var body = new BlockStmt();
        nf.setBody(body);
        cd.addMember(nf);
        final var etId = "$ENCLOSING_THIS";

        final var outerVars = services.getFinalVariables(cd);

        Parameter implictParameter = null;

        if (enclosingClass.isPresent()) {
            Optional<FieldDeclaration> et = getImplicitEnclosingThis(cd);
            ClassOrInterfaceDeclaration td = enclosingClass.get();
            if (et.isPresent()) {
                implictParameter = new Parameter(
                        new ClassOrInterfaceType(null, td.getName().getIdentifier()),
                        etId);
                var ca = new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(),
                                et.get().getVariables().get(0).getName().getIdentifier()),
                        implictParameter.getNameAsExpression(), AssignExpr.Operator.ASSIGN);

                parameters.add(implictParameter);
                body.addStatement(ca);
            }
        }

        // transfer the modification
        mods.addAll(TransformationPipelineServices.cloneList(cons.getModifiers()));

        // transfer the parameters
        parameters.addAll(TransformationPipelineServices.cloneList(cons.getParameters()));

        // transfer constructor body
        BlockStmt origBody = cons.getBody();
        if (origBody != null) {
            for (Statement statement : origBody.getStatements()) {
                body.addStatement(statement.clone());
            }
        }

        if (outerVars != null && !outerVars.isEmpty()) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }

            for (var v : outerVars) {
                parameters.add(new Parameter(services.getType(v.getType()), v.getName()));
            }
        }

        if (!cd.resolve().isJavaLangObject()) {
            // remember the original first statement
            Statement first = !body.getStatements().isEmpty() ? body.getStatement(0) : null;


            // call default constructor (super.$init())
            if (first == null || !first.isExplicitConstructorInvocationStmt()) {
                body.addStatement(0,
                        new MethodCallExpr(new SuperExpr(),
                                PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER));
            } else {
                // the first statement has to be a this or super constructor call
                // this(...) => this.$init(...)
                // or super(...) => super.$init(...)

                // The problem, is that we have to known if there is an implicit
                // outer variable.

                var constructorCall = (ExplicitConstructorInvocationStmt) first;

                if (constructorCall.isThis()) {
                    // On this we now, that we have to sent the implicit outer this.

                    var types =
                            constructorCall
                                    .getTypeArguments()
                                    .map(TransformationPipelineServices::cloneList)
                                    .orElse(new NodeList<>());

                    final NodeList<Expression> params =
                            TransformationPipelineServices.cloneList(constructorCall.getArguments());
                    if (implictParameter != null)
                        params.addFirst(implictParameter.getNameAsExpression());

                    var methodCall = new MethodCallExpr(new ThisExpr(),
                            types,
                            PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER,
                            params);
                    body.replace(first, new ExpressionStmt(methodCall));
                } else {
                    NodeList<Expression> args = constructorCall.getArguments();
                    /*
                    if (constructorCall.getExpression().isPresent()) {
                        if (args == null) args = new NodeList<>();
                        args.add((constructorCall.getExpression().get()));
                    } else if (!cd.resolve().getAllAncestors().isEmpty()) {
                        if (args == null) args = new NodeList<>();
                        args.add(new NameExpr(etId));
                    }
                    */
                    // TODO weigl: detect whether super is also an inner class. This class has to be an inner class
                    //  of the same outer class (JLS). If so, add $ENCLOSING_THIS to the parameters else not!

                    var type = ((ExplicitConstructorInvocationStmt) first).resolve().declaringType();
                    //var outer = JavaParserFacade.get().getTypeDeclaration(enclosingClass);
                    //var outerClass = outer.getClassName();
                    var className = type.getClassName();

                    //var container = type.containerType();//?
                    var expr = new MethodCallExpr(new SuperExpr(),
                            null,
                            PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER,
                            args);
                    body.replace(first, new ExpressionStmt(expr));
                }
            }

            if (outerVars != null) {
                for (ResolvedFieldDeclaration outerVar : outerVars) {
                    final var fieldAccessExpr = new FieldAccessExpr(new ThisExpr(),
                            PipelineConstants.FINAL_VAR_PREFIX + outerVar.getName());
                    var assign = new AssignExpr(fieldAccessExpr, new NameExpr(outerVar.getName()),
                            AssignExpr.Operator.ASSIGN);
                    body.addStatement(1, assign);
                }

                /*for (i = 0; i < initializers.size(); i++) {
                    body.addStatement(i + j + 1, initializers.get(i).clone());
                }*/
            }
        }
    }


    private Optional<ClassOrInterfaceDeclaration> getEnclosingClass(
            ClassOrInterfaceDeclaration cd) {
        if (cd.isNestedType()) {
            return cd.getParentNode().map(ClassOrInterfaceDeclaration.class::cast);
        }
        return Optional.empty();
    }

    @Nullable
    private ConstructorDeclaration attachConstructorDecl(TypeDeclaration<?> td) {
        if (td.getParentNode().get() instanceof ObjectCreationExpr) {
            var n = (ObjectCreationExpr) td.getParentNode().get();
            final var args = n.getArguments();
            if (args == null || args.size() == 0)
                return null;

            var type = n.getType().resolve();
            ConstructorDeclaration constructorDecl =
                    (ConstructorDeclaration) n.resolve().toAst().get();
            constructorDecl = constructorDecl.clone();

            final NodeList<Expression> cargs =
                    new NodeList<>(args.stream().map(Expression::clone).collect(Collectors.toList()));
            var sr = new MethodCallExpr(null, new NodeList<>(), new SimpleName("super"), cargs);
            constructorDecl.setBody(new BlockStmt(new NodeList<>(new ExpressionStmt(sr))));
            td.addMember(constructorDecl);
            return constructorDecl;
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
            if (cd.isInterface()) {
                return;
            }
            var constructors = td.getConstructors();
            ConstructorDeclaration anonConstr = null;
            if (cd.getName() == null) {
                anonConstr = attachConstructorDecl(td);
            }
            if (anonConstr != null)
                constructors.add(anonConstr);

            if (constructors.isEmpty()) {
                attachDefaultConstructor(cd);
            }

            for (ConstructorDeclaration constructor : constructors) {
                normalform(cd, constructor);
            }
        }
    }
}
