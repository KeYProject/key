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

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.VoidType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Each class is prepared before it is initialised. The preparation of
 * a class consists of pre-initialising the class fields with their
 * default values. This class creates the implicit method
 * <code>&lt;clprepare&gt;</code> responsible for the class
 * preparation.
 */
public class ClassPreparationMethodBuilder extends JavaTransformer {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ClassPreparationMethodBuilder.class);

    public static final String CLASS_PREPARE_IDENTIFIER = "$clprepare";

    /**
     * maps a class to its static NON-CONSTANT fields
     */
    private final HashMap<TypeDeclaration<?>, NodeList<Statement>> class2staticFields;

    /**
     * Creates an instance of the class preparation method model
     * transformer. Information about the current recoder model can be
     * accessed via the given service configuration. The implicit
     * preparation method is created and added for all classes,
     * which are declared in one of the given compilation units.
     *
     * @param services
     *        the CrossReferenceServiceConfiguration with the
     *        information about the recoder model
     */
    public ClassPreparationMethodBuilder(TransformationPipelineServices services) {
        super(services);
        class2staticFields = new LinkedHashMap<>(1024);
    }


    /**
     * retrieves all static non-constant fields and returns a list of
     * copy assignment pre-initialising them with their default values
     * <p>
     * some special settings for implicit fields are performed here as well
     *
     * @param typeDeclaration
     *        the TypeDeclaration<?> whose fields have to be prepared
     * @return the list of copy assignments
     */
    private NodeList<Statement> prepareFields(TypeDeclaration<?> typeDeclaration) {
        NodeList<Statement> result = new NodeList<>();
        List<FieldDeclaration> fields = typeDeclaration.getFields();
        for (FieldDeclaration spec : fields) {
            if (spec.isStatic() && spec.isFinal()) {
                for (VariableDeclarator variable : spec.getVariables()) {
                    if (services.isConstant(variable.getInitializer())) {
                        SimpleName ident = variable.getName();
                        result.add(
                            new ExpressionStmt(
                                new AssignExpr(
                                    new KeyPassiveExpression(
                                        new NameExpr(ident.clone())),
                                    services.getDefaultValue(variable.getType()),
                                    AssignExpr.Operator.ASSIGN)));
                    }
                }
            }
        }

        result.add(
            new ExpressionStmt(
                new AssignExpr(
                    new KeyPassiveExpression(
                        new NameExpr(PipelineConstants.IMPLICIT_CLASS_PREPARED)),
                    new BooleanLiteralExpr(true),
                    AssignExpr.Operator.ASSIGN)));
        return result;
    }

    public void prepare() {
        for (var cu : cache.getUnits()) {
            for (var td : cu.getTypes()) {
                boolean b = td.getMembers().stream()
                        .anyMatch(BodyDeclaration::isClassOrInterfaceDeclaration);

                if (b) {
                    LOGGER.debug(
                        "Inner Class detected. Reject building class initialisation methods.");
                }

                // collect initializers for transformation phase
                class2staticFields.put(td, prepareFields(td));
            }
        }
    }

    /**
     * creates the static method <code>&lt;clprepare&gt;</code> for the
     * given type declaration
     *
     * @param td
     *        the TypeDeclaration to which the new created method
     *        will be attached
     * @return the created class preparation method
     */
    private MethodDeclaration createPrepareMethod(TypeDeclaration<?> td) {
        NodeList<Modifier> modifiers = new NodeList<>(
            new Modifier(Modifier.Keyword.STATIC),
            new Modifier(Modifier.Keyword.PRIVATE));
        MethodDeclaration method = new MethodDeclaration(modifiers,
            new VoidType(), // return type is void
            CLASS_PREPARE_IDENTIFIER);
        final var statements = class2staticFields.get(td);
        if (statements != null) {
            method.setBody(new BlockStmt(statements));
        }
        return method;
    }


    /**
     * entry method for the constructor normalform builder
     *
     * @param td
     *        the TypeDeclaration
     */
    public void apply(TypeDeclaration<?> td) {
        td.addMember(createPrepareMethod(td));
    }
}
