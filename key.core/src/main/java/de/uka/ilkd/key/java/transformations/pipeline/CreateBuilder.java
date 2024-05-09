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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

import static de.uka.ilkd.key.java.transformations.AstFactory.*;

/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object
 * has to be created. In KeY this is quite similar to take it out of a list of
 * objects and setting the implicit flag <code> &lt;created&gt; </code> to
 * <code>true</code> as well as setting all fields of the object to their
 * default values. For the complete procedure, the method creates the
 * implicit method <code>&lt;createObject$gt;</code> which on its part calls
 * another implicit method <code>lt;prepare&gt;</code> for setting the fields
 * default values.
 */
public class CreateBuilder extends JavaTransformer {

    public static final String IMPLICIT_CREATE = "$create";

    public CreateBuilder(TransformationPipelineServices services) {
        super(services);
    }

    /**
     * Creates the body of the static <code>&lt;createObject&gt;</code>
     * method.
     */
    private BlockStmt createBody() {
        var block = new BlockStmt();
        block.addStatement(
            assign(attribute(new ThisExpr(), PipelineConstants.IMPLICIT_INITIALIZED),
                new BooleanLiteralExpr(false)));
        block.addStatement(call(PipelineConstants.IMPLICIT_OBJECT_PREPARE_ENTER));
        block.addStatement(new ReturnStmt(new ThisExpr()));
        return block;
    }


    /**
     * creates the implicit static <code>&lt;createObject&gt;</code>
     * method that takes the object to be created out of the pool
     *
     * @param type
     *        the TypeDeclaration for which the
     *        <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(TypeDeclaration<?> type) {
        NodeList<Modifier> modifiers = new NodeList<>();
        modifiers.add(new Modifier(Modifier.Keyword.PUBLIC));

        MethodDeclaration md = new MethodDeclaration(
            modifiers, new ClassOrInterfaceType(null, services.getId(type)),
            IMPLICIT_CREATE);
        md.setBody(createBody());
        return md;
    }


    /**
     * entry method for the constructor {@link ConstructorNormalformBuilder}
     *
     * @param td
     *        the TypeDeclaration
     */
    public void apply(TypeDeclaration<?> td) {
        if (td instanceof ClassOrInterfaceDeclaration
                && ((ClassOrInterfaceDeclaration) td).isInterface()) {
            // Interfaces can't have fields, so nothing to set
            return;
        }
        td.addMember(createMethod(td));
    }


}
