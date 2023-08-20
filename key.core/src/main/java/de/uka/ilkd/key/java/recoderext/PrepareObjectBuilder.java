/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;

import de.uka.ilkd.key.util.Debug;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.java.Identifier;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Protected;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.SuperReference;
import recoder.java.reference.ThisReference;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Creates the preparation method for pre-initilizing the object fields with their default settings.
 */
public class PrepareObjectBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_OBJECT_PREPARE = "<prepare>";

    public static final String IMPLICIT_OBJECT_PREPARE_ENTER = "<prepareEnter>";

    private final HashMap<TypeDeclaration, ASTList<Statement>> class2fields;

    private ClassType javaLangObject;


    public PrepareObjectBuilder(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
        class2fields = new LinkedHashMap<>(getUnits().size());
    }

    /**
     * returns all fields of the class cd in source code order. The method is a work around for a
     * bug in recoder 0.70 as there source code order is not respected. May become obsolete if newer
     * recoder versions are used.
     */
    private List<Field> getFields(ClassDeclaration cd) {
        List<Field> result = new ArrayList<>(cd.getChildCount());
        outer: for (int i = 0; i < cd.getChildCount(); i++) {
            if (cd.getChildAt(i) instanceof FieldDeclaration) {
                final FieldDeclaration fd = (FieldDeclaration) cd.getChildAt(i);
                for (Modifier mod : fd.getModifiers()) {
                    if (mod instanceof Model) {
                        continue outer;
                    }
                }
                final ASTList<FieldSpecification> fields = fd.getFieldSpecifications();
                result.addAll(fields);
            }
        }
        return result;
    }

    /**
     * Two-pass transformation have to be strictly divided up into two parts. the first part
     * analyzes the model and collects all necessary information. In this case all class
     * declarations are examined and for each found field a copy assignment to its default value is
     * added to the map "class2fields". All actions, which may cause a recoder model update have to
     * be done here.
     *
     * @return status report if analyze encountered problems or not
     */
    @Override
    public ProblemReport analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
        if (!(javaLangObject instanceof ClassDeclaration)) {
            Debug.fail("Could not find class java.lang.Object or only as bytecode");
        }
        for (final ClassDeclaration cd : classDeclarations()) {
            class2fields.put(cd, defaultSettings(getFields(cd)));
        }
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    /**
     * creates the assignments of the field variables to their default values and inserts them to
     * the given body list
     *
     * @return the same list body that has been handed over as parameter
     */
    private ASTList<Statement> defaultSettings(List<Field> fields) {

        if (fields == null) {
            return new ASTArrayList<>(0);
        }
        ASTList<Statement> result = new ASTArrayList<>(fields.size());
        for (Field field : fields) {
            if (!field.isStatic()) {
                Identifier fieldId;
                if (field.getName().charAt(0) != '<') {
                    fieldId = new Identifier(field.getName());
                    result.add(assign((attribute(new ThisReference(), fieldId)),
                        getDefaultValue(services.getCrossReferenceSourceInfo().getType(field))));
                }
            }
        }

        return result;
    }

    /**
     * creates an implicit method called 'prepare', that sets all attributes to their default values
     */
    protected StatementBlock createPrepareBody(ReferencePrefix prefix, TypeDeclaration classType) {
        ASTList<Statement> body = new ASTArrayList<>(15);

        if (classType != javaLangObject) {
            // we can access the implementation
            body.add((new MethodReference(new SuperReference(),
                new ImplicitIdentifier(IMPLICIT_OBJECT_PREPARE))));
            body.addAll(class2fields.get(classType));
        }
        return new StatementBlock(body);
    }

    /**
     * creates the implicit <code>&lt;prepare&gt;</code> method that sets the fields of the given
     * type to its default values
     *
     * @param type the TypeDeclaration for which the <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(TypeDeclaration type) {
        ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<>(1);
        modifiers.add(new Protected());
        MethodDeclaration md =
            new MethodDeclaration(modifiers, null, new ImplicitIdentifier(IMPLICIT_OBJECT_PREPARE),
                new ASTArrayList<>(0), null, createPrepareBody(new ThisReference(), type));
        md.makeAllParentRolesValid();
        return md;
    }

    /**
     * creates the implicit <code>&lt;prepareEnter&gt;</code> method that sets the fields of the
     * given type to its default values
     *
     * @param type the TypeDeclaration for which the <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethodPrepareEnter(TypeDeclaration type) {
        ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<>(1);
        modifiers.add(new Private());

        MethodDeclaration md = new MethodDeclaration(modifiers, null,
            new ImplicitIdentifier(IMPLICIT_OBJECT_PREPARE_ENTER), new ASTArrayList<>(0), null,
            createPrepareBody(new ThisReference(), type));
        md.makeAllParentRolesValid();
        return md;
    }


    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof ClassDeclaration) {
            attach(createMethod(td), td, td.getMembers().size());
            attach(createMethodPrepareEnter(td), td, td.getMembers().size());
        }
    }

}
