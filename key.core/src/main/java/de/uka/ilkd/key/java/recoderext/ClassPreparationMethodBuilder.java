/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.CrossReferenceServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Static;
import recoder.java.expression.literal.BooleanLiteral;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.FieldReference;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Each class is prepared before it is initialised. The preparation of a class consists of
 * pre-initialising the class fields with their default values. This class creates the implicit
 * method <code>&lt;clprepare&gt;</code> responsible for the class preparation.
 */
public class ClassPreparationMethodBuilder extends RecoderModelTransformer {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ClassPreparationMethodBuilder.class);

    public static final String CLASS_PREPARE_IDENTIFIER = "<clprepare>";

    /**
     * maps a class to its static NON CONSTANT fields
     */
    private final Map<TypeDeclaration, ASTList<Statement>> class2staticFields;

    /**
     * Creates an instance of the class preparation method model transformer. Information about the
     * current recoder model can be accessed via the given service configuration. The implicit
     * preparation method is created and added for all classes, which are declared in one of the
     * given compilation units.
     *
     * @param services the CrossReferenceServiceConfiguration with the information about the recoder
     *        model
     * @param cache a cache object that stores information which is needed by and common to many
     *        transformations. it includes the compilation units, the declared classes, and
     *        information for local classes.
     */
    public ClassPreparationMethodBuilder(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
        class2staticFields = new LinkedHashMap<>(10 * getUnits().size());
    }

    /**
     * returns true if the given fieldspecification denotes a constant field. A constant field is
     * declared as final and static and initialised with a time constant, which is not prepared or
     * initialised here. ATTENTION: this is a derivation from the JLS but the obtained behaviour is
     * equivalent as we only consider completely compiled programs and not partial compilations. The
     * reason for preparation and initialisation of comnpile time constant fields is due to binary
     * compatibility reasons.
     */
    private boolean isConstantField(FieldSpecification spec) {
        boolean result = spec.isStatic() && spec.isFinal();
        if (!result) {
            return false;
        }
        recoder.service.ConstantEvaluator ce = services.getConstantEvaluator();

        try {
            result = ce.isCompileTimeConstant(spec.getInitializer());
        } catch (ArithmeticException | NumberFormatException t) {
            result = false;
        }

        return result;
    }


    /**
     * retrieves all static non-constant fields and returns a list of copy assignment
     * pre-initialising them with their default values
     * <p>
     * some special settings for implicit fields are performed here as well
     *
     * @param typeDeclaration the ClassDeclaration whose fields have to be prepared
     * @return the list of copy assignments
     */
    private ASTList<Statement> prepareFields(TypeDeclaration typeDeclaration) {

        ASTList<Statement> result = new ASTArrayList<>(20);

        List<FieldSpecification> fields = typeDeclaration.getFieldsInScope();

        for (FieldSpecification spec : fields) {
            if (spec.isStatic() && !isConstantField(spec)) {
                Identifier ident = spec.getIdentifier();
                result.add(
                    new CopyAssignment(new PassiveExpression(new FieldReference(ident.deepClone())),
                        getDefaultValue(spec.getType())));
            }
        }

        result.add(new CopyAssignment(
            new PassiveExpression(new FieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_PREPARED))),
            new BooleanLiteral(true)));

        return result;
    }

    @Override
    public ProblemReport analyze() {
        for (final CompilationUnit cu : getUnits()) {
            final int typeCount = cu.getTypeDeclarationCount();
            for (int i = 0; i < typeCount; i++) {
                if (cu.getTypeDeclarationAt(i) instanceof ClassDeclaration) {
                    ClassDeclaration cd = (ClassDeclaration) cu.getTypeDeclarationAt(i);
                    if (cd.getTypeDeclarationCount() > 0) {
                        LOGGER.debug("clPrepBuilder: Inner Class detected. "
                            + "Reject building class initialisation methods.");
                    }

                    // collect initializers for transformation phase
                    class2staticFields.put(cd, prepareFields(cd));
                }
            }
        }
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    /**
     * creates the static method <code>&lt;clprepare&gt;</code> for the given type declaration
     *
     * @param td the TypeDeclaration to which the new created method will be attached
     * @return the created class preparation method
     */
    private MethodDeclaration createPrepareMethod(TypeDeclaration td) {
        ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<>(2);
        modifiers.add(new Static());
        modifiers.add(new Private());
        return new MethodDeclaration(modifiers, null, // return type is void
            new ImplicitIdentifier(CLASS_PREPARE_IDENTIFIER), new ASTArrayList<>(0), null, // no
                                                                                           // throws
            new StatementBlock(class2staticFields.get(td)));
    }


    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void makeExplicit(TypeDeclaration td) {
        attach(createPrepareMethod(td), td, 0);
    }
}
