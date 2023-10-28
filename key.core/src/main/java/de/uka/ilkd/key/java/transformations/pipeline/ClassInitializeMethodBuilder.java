/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

import java.util.Optional;


import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.VoidType;
import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.java.transformations.AstFactory.*;
import static de.uka.ilkd.key.java.transformations.pipeline.ClassPreparationMethodBuilder.CLASS_PREPARE_IDENTIFIER;

/**
 * Each class is prepared before it is initialised. The preparation of
 * a class consists of pre-initialising the class fields with their
 * default values. This class creates the implicit method
 * <code>&lt;clprepare&gt;</code> responsible for the class
 * preparation.
 */
public class ClassInitializeMethodBuilder extends JavaTransformer {
    public static final String CLASS_INITIALIZE_IDENTIFIER = "$clinit";

    /**
     * Creates an instance of the class preparation method model
     * transformer. Information about the current recoder model can be
     * accessed via the given service configuration. The implicit
     * preparation method is created and added for all classes,
     * which are declared in one of the given compilation units.
     *
     * @param services the CrossReferenceServiceConfiguration with the
     *        information about the recoder model
     */
    public ClassInitializeMethodBuilder(TransformationPipelineServices services) {
        super(services);
    }

    /**
     * returns true if the given fieldspecification denotes a constant
     * field. A constant field is declared as final and static and
     * initialised with a time constant, which is not prepared or
     * initialised here. ATTENTION: this is a derivation from the JLS
     * but the obtained behaviour is equivalent as we only consider
     * completely compiled programs and not partial compilations. The
     * reason for preparation and initialisation of comnpile time
     * constant fields is due to binary compatibility reasons.
     */
    private boolean isConstantField(FieldDeclaration spec, VariableDeclarator decl) {
        boolean result = spec.isStatic() && spec.isFinal();
        if (!result) {
            return false;
        }
        ConstantExpressionEvaluator ce = services.getConstantEvaluator();
        try {
            Optional<Expression> init = decl.getInitializer();
            if (init.isPresent()) {
                return ce.isCompileTimeConstant(init.get());
            } else {
                return false;
            }
        } catch (NumberFormatException | ArithmeticException | EvaluationException e) {
            return false;
        }
    }

    /**
     * iterates through the given field declaration and creates for each
     * specification that contains an initializer a corresponding copy
     * assignment. Thereby, only non-constant fields are considered.
     */
    private NodeList<Statement> fieldInitializersToAssignments(FieldDeclaration fd) {
        NodeList<VariableDeclarator> specs = fd.getVariables();
        NodeList<Statement> result = new NodeList<>();
        for (VariableDeclarator fs : specs) {
            if (fd.isStatic() && fs.getInitializer().isPresent() && !isConstantField(fd, fs)) {
                result.add(
                    new ExpressionStmt(
                        new AssignExpr(
                            new KeyPassiveExpression(new NameExpr(fs.getName())),
                            fs.getInitializer().get().clone(),
                            AssignExpr.Operator.ASSIGN

                        )));
            }
        }
        return result;

    }


    /**
     * retrieves all static non-constant fields and returns a list of
     * copy assignment pre-initialising them with their default values
     * <p>
     * some special settings for implicit fields are performed here as well
     *
     * @param typeDeclaration the TypeDeclaration<?> whose fields have to be prepared
     * @return the list of copy assignments
     */
    @NonNull
    private NodeList<Statement> getInitializers(@NonNull TypeDeclaration<?> typeDeclaration) {
        NodeList<Statement> result = new NodeList<>();
        for (Node childNode : typeDeclaration.getChildNodes()) {
            if (childNode instanceof InitializerDeclaration) {
                var init = (InitializerDeclaration) childNode;
                if (init.isStatic()) {
                    result.add(init.getBody().clone());
                }
            } else if (childNode instanceof FieldDeclaration) {
                result.addAll(fieldInitializersToAssignments((FieldDeclaration) childNode));
            }
        }
        return result;
    }

    /**
     * creates the following catch clause
     * <code><pre>
     * catch (<i>caughtType</i> <i>caughtParam</i>) {
     * &lt;classInitializationInProgress&gt;=false;
     * &lt;classClassErroneous&gt;=true;
     * t;
     * }</pre>
     * </code>
     */
    private CatchClause createCatchClause(String caughtType, String caughtParam, ThrowStmt t) {
        NodeList<Statement> catcher = new NodeList<>();
        var resetInitInProgress =
            assignToPassive(PipelineConstants.IMPLICIT_CLASS_INIT_IN_PROGRESS, mkTrue());
        var markErroneous = assignToPassive(PipelineConstants.IMPLICIT_CLASS_ERRONEOUS, mkTrue());

        Parameter param = new Parameter(
            services.getType("java", "lang", caughtType),
            caughtParam);

        catcher.add(resetInitInProgress);
        catcher.add(markErroneous);

        catcher.add(t);

        return new CatchClause(param, new BlockStmt(catcher));
    }

    /**
     * around the initializers there is a try block that catches
     * eventually thrown errors or exceptions and handles them in a
     * special way
     */
    @NonNull
    private TryStmt createInitializerExecutionTryBlock(@NonNull TypeDeclaration<?> td) {
        // try block
        NodeList<Statement> initializerExecutionBody = getInitializers(td);

        if (td instanceof ClassOrInterfaceDeclaration && !td.resolve().isJavaLangObject()) {
            var cd = (ClassOrInterfaceDeclaration) td;
            var type = cd.resolve();
            final var ancestors = type.getAncestors();
            if (!ancestors.isEmpty()) {
                final var superType = ancestors.get(0);
                final var scope = new NameExpr(superType.getQualifiedName());
                initializerExecutionBody.add(0,
                    callPassively(scope, CLASS_INITIALIZE_IDENTIFIER));
            }
        }

        // catch clauses
        var catchClauses = new NodeList<CatchClause>();
        catchClauses.add(
            mark(createCatchClause("Error", "err", throwName("err"))));

        var exceptionInInitializerArguments = new NodeList<Expression>();
        exceptionInInitializerArguments.add(new NameExpr(new SimpleName("twa")));

        ThrowStmt t = new ThrowStmt(
            new ObjectCreationExpr(null,
                services.getType("java", "lang", "ExceptionInInitializerError"),
                exceptionInInitializerArguments));

        catchClauses.add(createCatchClause("Throwable", "twa", t));

        return new TryStmt(new BlockStmt(initializerExecutionBody), catchClauses, null);
    }


    /**
     * creates the body of the initialize method
     */
    private BlockStmt createInitializeMethodBody(TypeDeclaration<?> td) {
        var methodBody = new NodeList<Statement>();
        var clInitializeBody = new NodeList<Statement>();
        var clInitNotInProgressBody = new NodeList<Statement>();

        var clNotPreparedBody = new NodeList<Statement>();
        clNotPreparedBody.add(mark(callPassively(CLASS_PREPARE_IDENTIFIER)));


        var s = PipelineConstants.IMPLICIT_CLASS_PREPARED;
        clInitNotInProgressBody.add(
            ifthen(negate(namePassively(s)),
                block(clNotPreparedBody)));


        var clErroneousBody = new NodeList<Statement>();
        clErroneousBody.add(
            new ThrowStmt(
                new ObjectCreationExpr(null,
                    services.getType("java", "lang", "NoClassDefFoundError"),
                    new NodeList<>())));

        // IF $classErroneous : clErroneousBody : null
        clInitNotInProgressBody.add(
            ifthen(namePassively(PipelineConstants.IMPLICIT_CLASS_ERRONEOUS),
                block(clErroneousBody)));


        // @(CLASS_INIT_IN_PROGRESS) = true
        clInitNotInProgressBody.add(
            assignToPassive(PipelineConstants.IMPLICIT_CLASS_INIT_IN_PROGRESS, mkTrue()));


        // create try block in initialized method
        clInitNotInProgressBody.add(createInitializerExecutionTryBlock(td));
        clInitNotInProgressBody
                .add(assignToPassive(PipelineConstants.IMPLICIT_CLASS_INIT_IN_PROGRESS, mkFalse()));
        clInitNotInProgressBody
                .add(assignToPassive(PipelineConstants.IMPLICIT_CLASS_ERRONEOUS, mkFalse()));
        clInitNotInProgressBody
                .add(assignToPassive(PipelineConstants.IMPLICIT_CLASS_INITIALIZED, mkTrue()));

        clInitializeBody.add(ifthen(
            negate(namePassively(PipelineConstants.IMPLICIT_CLASS_INIT_IN_PROGRESS)),
            block(clInitNotInProgressBody)));

        methodBody.add(ifthen(negate(namePassively(PipelineConstants.IMPLICIT_CLASS_INITIALIZED)),
            block(clInitializeBody)));

        return block(methodBody);
    }

    /**
     * Creates a static method {@code $clprepare} for the given type declaration.
     * <p>
     * <code><pre>
     *     public static void $clprepare() {
     *          ${createInitializeMethod(TypeDeclaration)}
     *     }
     * </pre></code>
     *
     * @param td the TypeDeclaration to which the new created method
     *        will be attached
     * @return the created class preparation method
     * @see #createInitializeMethod(TypeDeclaration)
     */
    private MethodDeclaration createInitializeMethod(TypeDeclaration<?> td) {
        MethodDeclaration md = new MethodDeclaration(new NodeList<>(),
            new VoidType(),
            CLASS_INITIALIZE_IDENTIFIER);
        md.addModifier(Modifier.Keyword.STATIC, Modifier.Keyword.PUBLIC);
        md.setBody(createInitializeMethodBody(td));
        return md;
    }

    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    @Override
    public void apply(TypeDeclaration<?> td) {
        td.addMember(createInitializeMethod(td));
    }
}
