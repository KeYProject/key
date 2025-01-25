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
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;


/**
 * The Java DL requires some implicit fields and methods, that are
 * available in each Java class. The name of the implicit fields/methods
 * is usually enclosed between two angle brackets. To access them in a
 * uniform way, they are added as usual fields to the classes, in
 * particular this makes it possible to parse them in a natural way.
 * The ImplicitFieldAdder is responsible to add all implicit fields to
 * the type declarations of the model. As the implicit methods and only
 * them will access these fields, this transformer has to be executed
 * before the other transformers are called.
 */
public class ImplicitFieldAdder extends JavaTransformer {

    /**
     * flag set if java.lang.Object has been already transformed
     */
    private boolean transformedObject = false;

    /**
     * creates a transformation that adds all implicit fields,
     * for example <code>&lt;created&gt;</code>,
     * <code>&lt;initialized&gt;</code> and
     * <code>&lt;nextToCreate&gt;</code> etc.
     *
     * @param services
     *        the CrossReferenceServiceConfiguration to access
     *        model information
     */
    public ImplicitFieldAdder(TransformationPipelineServices services) {
        super(services);
    }

    /**
     * creates an implicit field of the given type and name
     *
     * @param typeName
     *        the name of the type of the new field to create
     * @param fieldName
     *        the name of the field
     * @param isStatic
     *        a boolean that is true if the field has to be
     *        created as static (class) field
     * @return the new created field declaration
     */
    public static FieldDeclaration createImplicitField(
            Type typeName, String fieldName, boolean isStatic, boolean isPrivate) {
        return createImplicitField(typeName, fieldName, isStatic, isPrivate, false);
    }

    public static FieldDeclaration createImplicitField(
            Type type, String fieldName, boolean isStatic, boolean isPrivate, boolean isFinal) {
        NodeList<Modifier> modifiers = new NodeList<>();
        if (isStatic) {
            modifiers.add(new Modifier(Modifier.Keyword.STATIC));
        }
        if (isPrivate) {
            modifiers.add(new Modifier(Modifier.Keyword.PRIVATE));
        } else {
            modifiers.add(new Modifier(Modifier.Keyword.PUBLIC));
        }

        if (isFinal) {
            modifiers.add(new Modifier(Modifier.Keyword.FINAL));
        }

        VariableDeclarator variable = new VariableDeclarator(type, fieldName);
        FieldDeclaration fd = new FieldDeclaration(modifiers, variable);
        fd.addAnnotation("javax.annotation.processing.Generated");
        return fd;
    }


    /**
     * The implicit fields divide up into two categories. Global fields
     * declared just in java.lang.Object and type specific one declared
     * in each reference type. This method adds the global ones.
     */
    private void addGlobalImplicitFields(TypeDeclaration<?> td) {
        // instance
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_INITIALIZED, false, false));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CREATED, false, false));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.INT),
            PipelineConstants.IMPLICIT_TRANSIENT, false, false));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_TRANSACTION_UPDATED, false, false));
    }


    /**
     * adds implicit fields to the given type declaration
     *
     * @param td
     *        the recoder.java.TypeDeclaration to be enriched with
     *        implicit fields
     */
    private void addImplicitFields(TypeDeclaration<?> td) {
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_INIT_IN_PROGRESS, true, true));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_ERRONEOUS, true, true));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_INITIALIZED, true, true));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_PREPARED, true, true));

        if (td instanceof ClassOrInterfaceDeclaration
                // TODO weigl not understand this
                // &&
                // (td.getName() == null || ((TypeDeclaration<?>) td).getStatementContainer() !=
                // null ||
                // td.getContainingReferenceType() != null) &&
                // (services.containingMethod(td) == null ||
                // !services.containingMethod(td).isStatic()) &&
                && !((ClassOrInterfaceDeclaration) td).isInterface()
                && td.isNestedType()
                && !td.isStatic()) {
            TypeDeclaration<?> container = (TypeDeclaration<?>) td.getParentNode().get();
            String id = container.getNameAsString();
            td.addField(new ClassOrInterfaceType(null, id),
                PipelineConstants.IMPLICIT_ENCLOSING_THIS, Modifier.Keyword.PRIVATE);
        }
    }

    protected void addClassInitializerStatusFields(TypeDeclaration<?> td) {
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_INIT_IN_PROGRESS, true, true));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_ERRONEOUS, true, true));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_INITIALIZED, true, true));
        td.addMember(createImplicitField(new PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
            PipelineConstants.IMPLICIT_CLASS_PREPARED, true, true));
    }

    private void addFieldsForFinalVars(TypeDeclaration<?> td) {
        final var vars = services.getFinalVariables(td);
        if (!vars.isEmpty()) {
            // not sure why, but doing it separated in two loops is much faster (for large programs)
            // then just in one
            // strangely, the effect is not measureable for e.g. the class init. fields...
            for (final var v : vars) {
                Type type = services.getType(v.getType());
                td.addMember(createImplicitField(
                    type, // TODO weigl check for arrays&co.
                    PipelineConstants.FINAL_VAR_PREFIX + v.getName(), false, true));
            }
        }
    }

    public void apply(TypeDeclaration<?> td) {
        if (!transformedObject && td.resolve().isJavaLangObject()) {
            addGlobalImplicitFields(td);
            transformedObject = true;
        }

        addImplicitFields(td);
        addFieldsForFinalVars(td);
    }

}
