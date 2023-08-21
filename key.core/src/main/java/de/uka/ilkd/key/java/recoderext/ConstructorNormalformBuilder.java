/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import de.uka.ilkd.key.util.Debug;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.*;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Public;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.expression.operator.New;
import recoder.java.reference.*;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Transforms the constructors of the given class to their normalform. The constructor normalform
 * can then be accessed via a methodcall <code>&lt;init&gt;<cons_args)</code>. The visibility of the
 * normalform is the same as for the original constructor.
 */
public class ConstructorNormalformBuilder extends RecoderModelTransformer {

    public static final String CONSTRUCTOR_NORMALFORM_IDENTIFIER = "<init>";

    public static final String OBJECT_INITIALIZER_IDENTIFIER = "<objectInitializer>";

    private final Map<ClassDeclaration, List<Constructor>> class2constructors;
    private final Map<ClassDeclaration, Field> class2enclosingThis;
    private final Map<ClassDeclaration, ClassDeclaration> class2enclosingClass;
    private final Map<ClassDeclaration, ASTList<Statement>> class2initializers;
    private final Map<ClassDeclaration, Identifier> class2identifier;
    private final Map<ClassDeclaration, ASTList<MethodDeclaration>> class2methodDeclaration;
    private final Map<ClassDeclaration, ClassType> class2superContainer;
    private final Map<Variable, Type> v2t;

    private ClassType javaLangObject;

    /**
     * creates the constructor normalform builder
     */
    public ConstructorNormalformBuilder(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
        List<CompilationUnit> units = getUnits();
        class2constructors = new LinkedHashMap<>(4 * units.size());
        class2initializers = new LinkedHashMap<>(10 * units.size());
        class2methodDeclaration = new LinkedHashMap<>(10 * units.size());
        class2enclosingThis = new LinkedHashMap<>(units.size());
        class2enclosingClass = new LinkedHashMap<>(units.size());
        class2identifier = new LinkedHashMap<>(units.size());
        class2superContainer = new LinkedHashMap<>(units.size());
        v2t = new LinkedHashMap<>(units.size());
    }


    /**
     * The list of statements is the smallest list that contains a copy assignment for each instance
     * field initializer of class cd, e.g. <code> i = 0; </code> for
     * <code> public int i = 0; </code> or a reference to the private method
     * <code>&lt;objectInitializer&gt;<i>i</i> refering to the i-th object
     * initializer of cd. These private declared methods are created on
     * the fly. Example for
     * <code>
     * class C {
     * int i = 0;
     * {
     * int j = 3;
     * i = j + 5;
     * }
     * <p>
     * public C () {} ...
     * }
     * </code> the following list of size two is returned <code>
     * [ i = 0;,  &lt;objectInitializer&gt;0(); ]
     * </code> where <code>
     * private &lt;objectInitializer&gt;0() {
     * int j = 3;
     * i = j + 5;
     * }
     * </code>
     *
     * @param cd the ClassDeclaration of which the initilizers have to be collected
     * @return the list of copy assignments and method references realising the initializers.
     */
    private ASTList<Statement> collectInitializers(ClassDeclaration cd) {
        ASTList<Statement> result = new ASTArrayList<>(20);
        ASTList<MethodDeclaration> mdl = new ASTArrayList<>(5);
        int childCount = cd.getChildCount();
        for (int i = 0; i < childCount; i++) {
            if (cd.getChildAt(i) instanceof ClassInitializer
                    && !((ClassInitializer) cd.getChildAt(i)).isStatic()) {

                ASTList<DeclarationSpecifier> mods = new ASTArrayList<>(1);
                mods.add(new Private());
                String name = OBJECT_INITIALIZER_IDENTIFIER + mdl.size();
                MethodDeclaration initializerMethod = new MethodDeclaration(mods, null, // return
                                                                                        // type is
                                                                                        // void
                    new ImplicitIdentifier(name), new ASTArrayList<>(0), null,
                    ((ClassInitializer) cd.getChildAt(i)).getBody().deepClone());
                initializerMethod.makeAllParentRolesValid();
                mdl.add(initializerMethod);
                result.add(new MethodReference(null, new ImplicitIdentifier(name)));
            } else if (cd.getChildAt(i) instanceof FieldDeclaration
                    && !((FieldDeclaration) cd.getChildAt(i)).isStatic()) {
                ASTList<FieldSpecification> specs =
                    ((FieldDeclaration) cd.getChildAt(i)).getFieldSpecifications();
                for (FieldSpecification spec : specs) {
                    Expression fieldInit;
                    if ((fieldInit = spec.getInitializer()) != null) {
                        CopyAssignment fieldCopy = new CopyAssignment(
                            new FieldReference(new ThisReference(), spec.getIdentifier()),
                            fieldInit.deepClone());
                        result.add(fieldCopy);
                    }
                }
            }
        }
        class2methodDeclaration.put(cd, mdl);
        return result;
    }

    /**
     * Two-pass transformation have to be strictly divided up into two parts. the first part
     * analyzes the model and collects all necessary information. In this case all class
     * declarations are examined and initializers as well as constructors are collected. All
     * actions, which may cause a recoder model update have to be done here.
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
            if (cd.getName() == null || cd.getStatementContainer() != null) {
                (new FinalOuterVarsCollector()).walk(cd);
            }
            // collect constructors for transformation phase
            List<Constructor> constructors = new ArrayList<>(10);
            constructors.addAll(services.getSourceInfo().getConstructors(cd));
            if (constructors.isEmpty() && (cd.getContainingClassType() != null && !cd.isStatic()
                    || cd.getName() == null || cd.getStatementContainer() != null)) {
                constructors.add(new DefaultConstructor(cd));
            }
            class2constructors.put(cd, constructors);

            class2identifier.put(cd, getId(cd));

            class2enclosingThis.put(cd, getImplicitEnclosingThis(cd));

            if (cd.getAllSupertypes().size() > 1
                    && (cd.getStatementContainer() != null || cd.getName() == null)) {
                class2superContainer.put(cd, cd.getAllSupertypes().get(1).getContainingClassType());
            }

            final List<Variable> finalVars = getLocalClass2FinalVar().get(cd);
            if (finalVars != null) {
                for (final Variable v : finalVars) {
                    v2t.put(v, v.getType());
                }
            }

            if (cd.getName() == null || cd.getStatementContainer() != null
                    || cd.getContainingClassType() != null && !cd.isStatic()) {
                class2enclosingClass.put(cd, containingClass(cd));
            }

            // collect initializers for transformation phase
            class2initializers.put(cd, collectInitializers(cd));
        }
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    protected Field getImplicitEnclosingThis(ClassDeclaration cd) {
        for (final Field f : cd.getAllFields()) {
            if (f.getName().equals(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS)) {
                return f;
            }
        }
        return null;
    }

    private void attachDefaultConstructor(ClassDeclaration cd) {
        ASTList<DeclarationSpecifier> mods = new ASTArrayList<>(5);
        ASTList<ParameterDeclaration> parameters;
        Throws recThrows;
        StatementBlock body;
        mods.add(new Public());
        parameters = new ASTArrayList<>(0);
        recThrows = null;
        body = new StatementBlock();
        body.setBody(new ASTArrayList<>());
        attach(new MethodReference(new SuperReference(),
            new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER)), body, 0);
        final Iterator<Statement> initializers = class2initializers.get(cd).iterator();
        for (int i = 0; initializers.hasNext(); i++) {
            attach(initializers.next().deepClone(), body, i + 1);
        }
        MethodDeclaration def = new MethodDeclaration(mods, null, // return type is void
            new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER), parameters, recThrows, body);
        def.makeAllParentRolesValid();
        attach(def, cd, 0);
    }

    /**
     * Creates the normalform of the given constructor, that is declared in class cd. For a detailed
     * description of the normalform to be built see the KeY Manual.
     *
     * @param cd the ClassDeclaration where the cons is declared
     * @param cons the Constructor to be transformed
     * @return the constructor normalform
     */
    private MethodDeclaration normalform(ClassDeclaration cd, Constructor cons) {

        ASTList<DeclarationSpecifier> mods = new ASTArrayList<>(5);
        ASTList<ParameterDeclaration> parameters;
        Throws recThrows;
        StatementBlock body;
        Field et = class2enclosingThis.get(cd);
        TypeDeclaration td = class2enclosingClass.get(cd);
        final List<Variable> outerVars = getLocalClass2FinalVar().get(cd);
        int j = et == null ? 0 : 1;
        if (outerVars != null) {
            j += outerVars.size();
        }
        ParameterDeclaration pd = null;
        CopyAssignment ca = null;
        String etId = "_ENCLOSING_THIS";
        if (et != null) {
            pd = new ParameterDeclaration(new TypeReference(td.getIdentifier().deepClone()),
                new Identifier(etId));
            ca = new CopyAssignment(
                new FieldReference(new ThisReference(), new ImplicitIdentifier(et.getName())),
                new VariableReference(new Identifier(etId)));
        }

        if (!(cons instanceof ConstructorDeclaration)) {
            mods.add(new Public());
            parameters = new ASTArrayList<>(j);
            recThrows = null;
            body = new StatementBlock();
        } else {
            ConstructorDeclaration consDecl = (ConstructorDeclaration) cons;
            mods = (consDecl.getDeclarationSpecifiers() == null ? null
                    : consDecl.getDeclarationSpecifiers().deepClone());
            parameters = consDecl.getParameters().deepClone();
            recThrows = consDecl.getThrown() == null ? null : consDecl.getThrown().deepClone();

            StatementBlock origBody = consDecl.getBody();
            if (origBody == null) // may happen if a stub is defined with an empty constructor
            {
                body = null;
            } else {
                body = origBody.deepClone();
            }
        }

        if (outerVars != null && !outerVars.isEmpty()) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }

            for (final Variable v : outerVars) {
                parameters.add(new ParameterDeclaration(
                    new TypeReference(new Identifier(v2t.get(v).getName())),
                    new Identifier(v.getName())));
            }
        }

        if (pd != null) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }
            parameters.add(pd);
        }

        if (cd != javaLangObject && body != null) {
            // remember original first statement
            Statement first = body.getStatementCount() > 0 ? body.getStatementAt(0) : null;

            // first statement has to be a this or super constructor call
            if (!(first instanceof SpecialConstructorReference)) {
                if (body.getBody() == null) {
                    body.setBody(new ASTArrayList<>());
                }
                attach(new MethodReference(new SuperReference(),
                    new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER)), body, 0);
            } else {
                body.getBody().remove(0);
                if (first instanceof ThisConstructorReference) {
                    attach(new MethodReference(new ThisReference(),
                        new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER),
                        ((SpecialConstructorReference) first).getArguments()), body, 0);
                } else {
                    ReferencePrefix referencePrefix =
                        ((SuperConstructorReference) first).getReferencePrefix();
                    ASTList<Expression> args = ((SpecialConstructorReference) first).getArguments();
                    if (referencePrefix instanceof Expression) {
                        if (args == null) {
                            args = new ASTArrayList<>(1);
                        }
                        args.add((Expression) referencePrefix);
                    } else if (class2superContainer.get(cd) != null) {
                        if (args == null) {
                            args = new ASTArrayList<>(1);
                        }
                        args.add(new VariableReference(new Identifier(etId)));
                    }
                    attach(
                        new MethodReference(new SuperReference(),
                            new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER), args),
                        body, 0);
                }
            }
            // if the first statement is not a this constructor reference
            // the instance initializers have to be added in source code
            // order
            if (!(first instanceof ThisConstructorReference)) {
                ASTList<Statement> initializers = class2initializers.get(cd);
                if (ca != null) {
                    attach(ca, body, 0);
                }
                for (int i = 0; outerVars != null && i < outerVars.size(); i++) {
                    attach(
                        new CopyAssignment(
                            new FieldReference(new ThisReference(),
                                new ImplicitIdentifier(ImplicitFieldAdder.FINAL_VAR_PREFIX
                                        + (outerVars.get(i)).getName())),
                            new VariableReference(new Identifier(outerVars.get(i).getName()))),
                        body, i + (ca != null ? 1 : 0));
                }
                for (int i = 0; i < initializers.size(); i++) {
                    attach(initializers.get(i).deepClone(), body, i + 1 + j);
                }

            }
        }


        MethodDeclaration nf = new MethodDeclaration(mods, null, // return type is void
            new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER), parameters, recThrows, body);
        nf.makeAllParentRolesValid();
        return nf;
    }

    private ConstructorDeclaration attachConstructorDecl(TypeDeclaration td) {
        if (td.getASTParent() instanceof New) {
            New n = (New) td.getASTParent();
            if (n.getArguments() == null || n.getArguments().isEmpty()) {
                return null;
            }
            ConstructorDeclaration constr =
                services.getCrossReferenceSourceInfo().getConstructorDeclaration(
                    services.getCrossReferenceSourceInfo().getConstructor(n));
            constr = constr.deepClone();
            SuperConstructorReference sr = new SuperConstructorReference(
                n.getArguments() != null ? n.getArguments().deepClone() : new ASTArrayList<>(0));
            constr.setBody(new StatementBlock(new ASTArrayList<>(sr)));
            constr.makeAllParentRolesValid();
            attach(constr, td, 0);
            return constr;
        }
        return null;
    }

    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof ClassDeclaration) {
            List<Constructor> constructors = class2constructors.get(td);
            ConstructorDeclaration anonConstr = null;
            if (td.getName() == null) {
                anonConstr = attachConstructorDecl(td);
            }
            if (anonConstr != null) {
                constructors.add(anonConstr);
            }
            for (Constructor constructor : constructors) {
                attach(normalform((ClassDeclaration) td, constructor), td, 0);
            }

            ASTList<MethodDeclaration> mdl = class2methodDeclaration.get(td);
            for (MethodDeclaration methodDeclaration : mdl) {
                attach(methodDeclaration, td, 0);
            }
        }
    }
}
