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

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.JavaDLFieldNames;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.VoidType;

import static de.uka.ilkd.key.java.transformations.AstFactory.assign;
import static de.uka.ilkd.key.java.transformations.AstFactory.attribute;
import static de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants.IMPLICIT_OBJECT_PREPARE;
import static de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants.IMPLICIT_OBJECT_PREPARE_ENTER;

/**
 * Creates the preparation method for pre-initilizing the object fields
 * with their default settings.
 */
public class PrepareObjectBuilder extends JavaTransformer {
    public PrepareObjectBuilder(TransformationPipelineServices services) {
        super(services);
    }

    /**
     * returns all fields of the class cd in source code order. The
     * method is a work around for a bug in recoder 0.70 as there source
     * code order is not respected. May become obsolete if newer recoder
     * versions are used.
     */
    private List<VariableDeclarator> getFields(TypeDeclaration<?> cd) {
        List<VariableDeclarator> result = new ArrayList<>();
        outer: for (FieldDeclaration fd : cd.getFields()) {
            for (Modifier mod : fd.getModifiers()) {
                if (mod.getKeyword() == Modifier.Keyword.MODEL)
                    continue outer;
            }
            var fields = fd.getVariables();
            result.addAll(fields);
        }
        return result;
    }

    /**
     * creates the assignments of the field variables to their default values
     * and inserts them to the given body list
     *
     * @return the same list body that has been handed over as parameter
     */
    private NodeList<Statement> defaultSettings(List<FieldDeclaration> fields) {
        if (fields == null) {
            return new NodeList<>();
        }
        NodeList<Statement> result = new NodeList<Statement>();
        for (FieldDeclaration field : fields) {
            if (!field.isStatic()) {
                for (VariableDeclarator variable : field.getVariables()) {
                    SimpleName fieldId = variable.getName();
                    if (!fieldId.getIdentifier().startsWith("" + JavaDLFieldNames.FIELD_PREFIX
                        + JavaDLFieldNames.IMPLICIT_NAME_PREFIX)) {
                        for (final VariableDeclarator fieldDecl : field.getVariables()) {
                            final var defaultValue =
                                services.getDefaultValue(fieldDecl.getType());
                            if (defaultValue == null) {
                                throw new RuntimeException(
                                    "Default value for " + field.resolve().getType() + " is null");
                            } else {
                                result.add(
                                    assign((attribute(new ThisExpr(), fieldId.getIdentifier())),
                                        defaultValue));
                            }
                        }
                    }
                }
            }
        }
        return result;
    }

    /**
     * creates an implicit method called 'prepare', that sets all
     * attributes to their default values
     */
    protected BlockStmt createPrepareBody(TypeDeclaration<?> type) {
        var body = new NodeList<Statement>();
        if (!type.resolve().isJavaLangObject()) {
            // we can access the implementation
            body.add(
                new ExpressionStmt(new MethodCallExpr(new SuperExpr(), IMPLICIT_OBJECT_PREPARE)));
            body.addAll(defaultSettings(type.getFields()));
        }
        return new BlockStmt(body);
    }

    /**
     * creates the implicit <code>&lt;prepare&gt;</code> method that
     * sets the fields of the given type to its default values
     *
     * @param type
     *        the TypeDeclaration for which the
     *        <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(TypeDeclaration type) {
        NodeList<Modifier> modifiers =
            new NodeList<Modifier>(new Modifier(Modifier.Keyword.PROTECTED));
        MethodDeclaration md = new MethodDeclaration(modifiers,
            new VoidType(),
            IMPLICIT_OBJECT_PREPARE);
        md.setBody(createPrepareBody(type));
        return md;
    }

    /**
     * creates the implicit <code>&lt;prepareEnter&gt;</code> method that
     * sets the fields of the given type to its default values
     *
     * @param type
     *        the TypeDeclaration for which the
     *        <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethodPrepareEnter(TypeDeclaration<?> type) {
        NodeList<Modifier> modifiers = new NodeList<>(new Modifier(Modifier.Keyword.PRIVATE));
        MethodDeclaration md = new MethodDeclaration(modifiers,
            new VoidType(),
            IMPLICIT_OBJECT_PREPARE_ENTER);
        md.setBody(createPrepareBody(type));
        return md;
    }


    /**
     * entry method for the constructor normalform builder
     *
     * @param td
     *        the TypeDeclaration
     */
    public void apply(TypeDeclaration<?> td) {
        if (td instanceof ClassOrInterfaceDeclaration
                && !((ClassOrInterfaceDeclaration) td).isInterface()) {
            td.addMember(createMethod(td));
            td.addMember(createMethodPrepareEnter(td));
        }
    }

}
