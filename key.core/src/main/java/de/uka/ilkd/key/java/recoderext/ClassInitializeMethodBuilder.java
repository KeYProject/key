/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.util.Debug;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.expression.literal.BooleanLiteral;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.expression.operator.LogicalNot;
import recoder.java.expression.operator.New;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Each class is prepared before it is initialised. The preparation of a class consists of
 * pre-initialising the class fields with their default values. This class creates the implicit
 * method <code>&lt;clprepare&gt;</code> responsible for the class preparation.
 */
public class ClassInitializeMethodBuilder extends RecoderModelTransformer {

    public static final String CLASS_INITIALIZE_IDENTIFIER = "<clinit>";

    /**
     * maps a class to its static NON CONSTANT fields
     */
    private final Map<TypeDeclaration, ASTList<Statement>> class2initializers;

    /**
     * maps a class to its superclass
     */
    private final Map<ClassDeclaration, TypeReference> class2super;

    private ClassType javaLangObject;


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
    public ClassInitializeMethodBuilder(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
        class2initializers = new LinkedHashMap<>(10 * getUnits().size());
        class2super = new LinkedHashMap<>(2 * getUnits().size());
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
        } catch (NumberFormatException | ArithmeticException e) {
            result = false;
        }

        return result;
    }

    /**
     * creates the package reference java.lang
     */
    private PackageReference createJavaLangPackageReference() {
        return new PackageReference(new PackageReference(new Identifier("java")),
            new Identifier("lang"));
    }


    /**
     * iterates through the given field declaration and creates for each specification that contains
     * an initializer a corresponding copy assignment. Thereby only non-constant fields are
     * considered.
     */
    private ASTList<Statement> fieldInitializersToAssignments(FieldDeclaration fd) {

        ASTList<FieldSpecification> specs = fd.getFieldSpecifications();
        ASTList<Statement> result = new ASTArrayList<>(specs.size());

        for (FieldSpecification fs : specs) {
            if (fs.isStatic() && fs.getInitializer() != null && !isConstantField(fs)) {
                result.add(assign(passiveFieldReference(fs.getIdentifier().deepClone()),
                    fs.getInitializer().deepClone()));
            }
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
    private ASTList<Statement> getInitializers(TypeDeclaration typeDeclaration) {

        ASTList<Statement> result = new ASTArrayList<>(typeDeclaration.getChildCount());

        for (int i = 0; i < typeDeclaration.getChildCount(); i++) {
            if (typeDeclaration.getChildAt(i) instanceof ClassInitializer) {
                result.add(
                    ((ClassInitializer) typeDeclaration.getChildAt(i)).getBody().deepClone());
            } else if (typeDeclaration.getChildAt(i) instanceof FieldDeclaration) {
                result.addAll(fieldInitializersToAssignments(
                    (FieldDeclaration) typeDeclaration.getChildAt(i)));
            }
        }
        return result;
    }

    @Override
    public ProblemReport analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
        if (!(javaLangObject instanceof ClassDeclaration)) {
            Debug.fail("Could not find class java.lang.Object or only as bytecode");
        }
        for (final ClassDeclaration cd : classDeclarations()) {
            class2initializers.put(cd, getInitializers(cd));
            if (cd != javaLangObject) {
                TypeReference superType;
                if (cd.getExtendedTypes() != null) {
                    superType = cd.getExtendedTypes().getTypeReferenceAt(0).deepClone();
                } else {
                    superType = new TypeReference(createJavaLangPackageReference(),
                        new Identifier("Object"));
                }
                class2super.put(cd, superType);
            }
        }
        for (int unit = 0; unit < getUnits().size(); unit++) {
            CompilationUnit cu = getUnits().get(unit);
            int typeCount = cu.getTypeDeclarationCount();

            for (int i = 0; i < typeCount; i++) {
                TypeDeclaration td = cu.getTypeDeclarationAt(i);
                if (!(td instanceof ClassDeclaration)) {
                    class2initializers.put(td, getInitializers(td));
                }
            }

        }
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }


    /**
     * creates passive field reference access
     */
    protected PassiveExpression passiveFieldReference(Identifier id) {
        return new PassiveExpression(new FieldReference(id));
    }


    /**
     * creates a recoder copy assignment
     */
    @Override
    protected CopyAssignment assign(Expression left, Expression right) {
        return new CopyAssignment(left, right);
    }


    /**
     * creates the following catch clause <code>
     * catch (<i>caughtType</i> <i>caughtParam</i>) {
     * &lt;classInitializationInProgress&gt;=false;
     * &lt;classClassErroneous&gt;=true;
     * t;
     * }
     * </code>
     */
    private Catch createCatchClause(String caughtType, String caughtParam, Throw t) {

        ASTList<Statement> catcher = new ASTArrayList<>(3);

        CopyAssignment resetInitInProgress = assign(
            passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS)),
            new BooleanLiteral(false));

        CopyAssignment markErroneous = assign(
            passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS)),
            new BooleanLiteral(true));

        ParameterDeclaration param = new ParameterDeclaration(
            new TypeReference(createJavaLangPackageReference(), new Identifier(caughtType)),
            new Identifier(caughtParam));


        catcher.add(resetInitInProgress.deepClone());
        catcher.add(markErroneous.deepClone());

        catcher.add(t);

        return new Catch(param, new StatementBlock(catcher));
    }


    /**
     * around the initializers there is a try block that catches eventually thrown errors or
     * exceptions and handles them in a special way
     */
    private Try createInitializerExecutionTryBlock(TypeDeclaration td) {

        // try block
        ASTList<Statement> initializerExecutionBody;

        initializerExecutionBody = class2initializers.get(td);
        if (initializerExecutionBody == null) {
            initializerExecutionBody = new ASTArrayList<>(20);
        }

        if (td instanceof ClassDeclaration && td != javaLangObject) {
            ClassDeclaration cd = (ClassDeclaration) td;
            initializerExecutionBody.add(0, new PassiveExpression(new MethodReference(
                class2super.get(cd).deepClone(),
                new ImplicitIdentifier(ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER))));
        }

        // catch clauses


        ASTList<Branch> catchClauses = new ASTArrayList<>(2);

        catchClauses.add(createCatchClause("Error", "err",
            new Throw(new VariableReference(new Identifier("err")))));

        ASTList<Expression> exceptionInInitializerArguments = new ASTArrayList<>(1);
        exceptionInInitializerArguments.add(new VariableReference(new Identifier("twa")));

        Throw t =
            new Throw(new New(null,
                new TypeReference(createJavaLangPackageReference(),
                    new Identifier("ExceptionInInitializerError")),
                exceptionInInitializerArguments));

        catchClauses.add(createCatchClause("Throwable", "twa", t));

        return new Try(new StatementBlock(initializerExecutionBody), catchClauses);
    }


    /**
     * creates the body of the initialize method
     */
    private StatementBlock createInitializeMethodBody(TypeDeclaration td) {

        ASTList<Statement> methodBody = new ASTArrayList<>(1);
        ASTList<Statement> clInitializeBody = new ASTArrayList<>(2);
        ASTList<Statement> clInitNotInProgressBody = new ASTArrayList<>(20);

        ASTList<Statement> clNotPreparedBody = new ASTArrayList<>(1);
        clNotPreparedBody.add(new PassiveExpression(new MethodReference(
            new ImplicitIdentifier(ClassPreparationMethodBuilder.CLASS_PREPARE_IDENTIFIER))));

        If isClassPrepared = new If(
            new LogicalNot(passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_PREPARED))),
            new Then(new StatementBlock(clNotPreparedBody)));


        clInitNotInProgressBody.add(isClassPrepared);


        ASTList<Statement> clErroneousBody = new ASTArrayList<>(1);
        clErroneousBody
                .add(new Throw(new New(null, new TypeReference(createJavaLangPackageReference(),
                    new Identifier("NoClassDefFoundError")), null)));
        If isClassErroneous = new If(
            passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS)),
            new Then(new StatementBlock(clErroneousBody)));


        clInitNotInProgressBody.add(isClassErroneous);


        // @(CLASS_INIT_IN_PROGRESS) = true
        clInitNotInProgressBody.add(assign(
            passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS)),
            new BooleanLiteral(true)));


        // create try block in initialize method
        clInitNotInProgressBody.add(createInitializerExecutionTryBlock(td));
        clInitNotInProgressBody.add(assign(
            passiveFieldReference(
                (new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS))),
            new BooleanLiteral(false)));
        clInitNotInProgressBody.add(assign(
            passiveFieldReference(
                (new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS))),
            new BooleanLiteral(false)));
        clInitNotInProgressBody.add(assign(
            passiveFieldReference(
                (new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED))),
            new BooleanLiteral(true)));


        If isClassInitializationInProgress = new If(
            new LogicalNot(passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS))),
            new Then(new StatementBlock(clInitNotInProgressBody)));


        clInitializeBody.add(isClassInitializationInProgress);
        If isClassInitialized = new If(
            new LogicalNot(passiveFieldReference(
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED))),
            new Then(new StatementBlock(clInitializeBody)));

        methodBody.add(isClassInitialized);

        return new StatementBlock(methodBody);
    }


    /**
     * creates the static method <code>&lt;clprepare&gt;</code> for the given type declaration
     *
     * @param td the TypeDeclaration to which the new created method will be attached
     * @return the created class preparation method
     */
    private MethodDeclaration createInitializeMethod(TypeDeclaration td) {
        ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<>(2);
        modifiers.add(new Static());
        modifiers.add(new Public());
        return new MethodDeclaration(modifiers, null,
            new ImplicitIdentifier(CLASS_INITIALIZE_IDENTIFIER), new ASTArrayList<>(0), null,
            createInitializeMethodBody(td));
    }


    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void makeExplicit(TypeDeclaration td) {
        attach(createInitializeMethod(td), td, 0);
    }


}
