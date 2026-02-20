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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.KeyMethodBodyStatement;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

import static de.uka.ilkd.key.java.transformations.AstFactory.*;

/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object
 * has to be created, in KeY this is quite similar to take it out of a list of
 * objects and setting the implicit flag <code> &lt;created&gt; </code> to
 * <code>true</code> as well as setting all fields of the object to their
 * default values. For the complete procedure, the method creates the
 * implicit method <code>&lt;createObject$gt;</code> which on its part calls
 * another implicit method <code>lt;prepare&gt;</code> for setting the fields
 * default values.
 */
public class CreateObjectBuilder extends JavaTransformer {

    public static final String IMPLICIT_OBJECT_CREATE = "$createObject";
    public static final String NEW_OBJECT_VAR_NAME = "__NEW__";
    private final HashMap<TypeDeclaration<?>, SimpleName> class2SimpleName;


    public CreateObjectBuilder(TransformationPipelineServices services) {
        super(services);
        class2SimpleName = new LinkedHashMap<>();
    }


    /**
     * Creates the body of the static <code>&lt;createObject&gt;</code>
     * method.
     */
    private BlockStmt createBody(ClassOrInterfaceDeclaration recoderClass) {
        var result = new BlockStmt();
        final var thisType = services.getType(recoderClass);
        var local = new VariableDeclarationExpr(thisType, NEW_OBJECT_VAR_NAME);
        result.addStatement(local);

        var arguments = new NodeList<Expression>();

        result.addStatement(
            assign(name(NEW_OBJECT_VAR_NAME),
                call(new TypeExpr(thisType), PipelineConstants.IMPLICIT_INSTANCE_ALLOCATE,
                    arguments)));

        MethodCallExpr createRef =
            new MethodCallExpr(new NameExpr(NEW_OBJECT_VAR_NAME), CreateBuilder.IMPLICIT_CREATE);

        // July 08 - mulbrich: wraps createRef into a method body statement to
        // avoid unnecessary dynamic dispatch.
        // Method body statement are not possible for anonymous classes, however.
        // Use a method call there
        if (recoderClass.getName() == null) {// TODO weigl recheck
            // anonymous
            result.addStatement(
                new MethodCallExpr(new NameExpr(new SimpleName(NEW_OBJECT_VAR_NAME)),
                    CreateBuilder.IMPLICIT_CREATE));
        } else {
            result.addStatement(new KeyMethodBodyStatement(null, createRef, thisType));
        }

        // TODO javaparser why does the method return a value? Is the result ever used??
        result.addStatement(new ReturnStmt(new NameExpr(NEW_OBJECT_VAR_NAME)));
        return result;
    }



    /**
     * appends and creates the implicit static <code>&lt;createObject&gt;</code>
     * method that takes the object to be created out of the pool
     */
    public void createMethod(ClassOrInterfaceDeclaration type) {
        var md = type.addMethod(
            IMPLICIT_OBJECT_CREATE,
            Modifier.Keyword.PUBLIC, Modifier.Keyword.STATIC);
        md.setType(new ClassOrInterfaceType(null, type.getName(), null));
        md.setBody(createBody(type));
    }

    public void prepare() {}

    /**
     * entry method for the constructor normalform builder
     *
     * @param td
     *        the TypeDeclaration
     */
    public void apply(TypeDeclaration<?> td) {
        if (td instanceof ClassOrInterfaceDeclaration
                && !((ClassOrInterfaceDeclaration) td).isInterface()) {
            createMethod((ClassOrInterfaceDeclaration) td);
        }
    }


}
