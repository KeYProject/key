// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.removegenerics;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.ProblemReport;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.SourceInfo;

class ResolveTypeDeclaration extends GenericResolutionTransformation {

    private TypeDeclaration declaration;

    private List<MethodDeclaration> methodsToAdd = new ArrayList<MethodDeclaration>();
    private List<List<Type>> signaturesToAdd = new ArrayList<List<Type>>();

    public ResolveTypeDeclaration(ClassDeclaration declaration, CrossReferenceServiceConfiguration sc) {
        super(sc);
        this.declaration = declaration;
    }

    public ResolveTypeDeclaration(InterfaceDeclaration declaration, CrossReferenceServiceConfiguration sc) {
        super(sc);
        this.declaration = declaration;
    }

    @Override
    public ProblemReport analyze() {

        ASTList<TypeParameterDeclaration> typeParameters = declaration.getTypeParameters();

        if (typeParameters == null || typeParameters.isEmpty()) {
            setProblemReport(IDENTITY);
        } else {
            setProblemReport(EQUIVALENCE);
        }

        analyseMethods();

        return getProblemReport();

    }

    void analyseMethods() {
//        ClassType classType = (ClassType) getSourceInfo().getType(declaration);
//        System.err.println("===\nMethods for " + classType + " (" + declaration + ") " + System.identityHashCode(declaration));

        for (Method method : declaration.getMethods()) {
            List<Type> signature = method.getSignature();
            List<Method> superMethods = getOverriddenMethods(method);
            List<Type> ungenericSignature = getUngenericSignature(signature);

            // ignore static methods
            if (method.isStatic())
                continue;

             debugOut("---");
             debugOut("Method", method);
             debugOut("Type", signature);
             debugOut("ungeneric Type", ungenericSignature);
             debugOut("superMethods", superMethods);

            for (Method superMethod : superMethods) {
                List<Type> ungenericSuperSignature = getUngenericSignature(superMethod.getSignature());

                boolean isStatic = superMethod.isStatic();
                boolean differentSigs = !ungenericSuperSignature.equals(ungenericSignature);
                boolean alreadyPresent = methodAlreadyPresent(method.getName(), ungenericSuperSignature);
                if (!isStatic && differentSigs && !alreadyPresent) {
                    setProblemReport(EQUIVALENCE);
                    addMethod(method, ungenericSignature, ungenericSuperSignature);
                }
            }

        }

    }

    /**
     * check if this new method has already been added to the class or has been
     * present in the first place!
     * 
     * @param name
     * @param signature
     * @return a boolean true if the method with the given name and signature existed already
     */
    private boolean methodAlreadyPresent(String name, List<Type> signature) {
        
        //
        // has always been there
        for (Method m : getSourceInfo().getAllMethods(declaration)) {
            List<Type> mdSig = m.getSignature();
            if(m.getName().equals(name) && signature.equals(mdSig))
                return true;
        }
        
        //
        // the signatures are stored
        int i = 0;
        for (MethodDeclaration md : methodsToAdd) {
            List<Type> mdSig = signaturesToAdd.get(i++); 
            if(md.getName().equals(name) && signature.equals(mdSig))
                return true;
        }
        
        return false;
    }

    /**
     * create a wrapping method for a method with incompatible signatures.
     * 
     * If a class overrides a method in a generic context, this method may be
     * more specific than inheritance allows. To mimic this behaviour under
     * java4 new methods have to be introduced. Example:
     * 
     * <pre>
     * interface A<E,F> { void m(E e, F f); }
     * class B<E> implements A<E, Integer> { void m(E e, Integer f) {} } 
     * </pre>
     * 
     * The method in class B does not override the one in A. Instead, a method
     * 
     * <pre>
     * void m(Object arg1, Object arg2) { m((Object)arg1, (Integer)arg2); }
     * </pre>
     * 
     * has to be introduced.
     * 
     * TODO What if a method is static, yet in a subclass not static
     * 
     * TODO What if a method is static in a subclass
     * 
     * @param origMethod
     *            some onformation (visibility, return type, ...) is taken from
     *            here
     * @param localSign
     *            this is the signature of the method after removal of TV
     * @param superSig
     *            this is the target signature of the supertype.
     */
    private void addMethod(Method origMethod, List<Type> localSign, List<Type> superSig) {
        ProgramFactory programFactory = getProgramFactory();

        //
        // do not clone static methods!
        assert !origMethod.isStatic();

        //
        // make what is needed to define a method
        Type returnType = targetType(origMethod.getReturnType());
        String name = origMethod.getName();
        ASTList<DeclarationSpecifier> prefix = getDeclarationSpecifiers(origMethod);
        List<ClassType> exceptions = new ArrayList<ClassType>(origMethod.getExceptions());
        Throws _throws = createThrows(exceptions);
        TypeReference returnTypeRef = null;
        if (returnType != null)
            returnTypeRef = TypeKit.createTypeReference(programFactory, returnType);
        else
            returnTypeRef = TypeKit.createTypeReference(programFactory, "void");
        Identifier methodName = programFactory.createIdentifier(name);

        //
        // make the paramters: the ones of the super class
        ASTList<ParameterDeclaration> parameters = new ASTArrayList<ParameterDeclaration>();
        int counter = 1;
        for (Type type : superSig) {
            TypeReference typeRef = TypeKit.createTypeReference(programFactory, type);
            Identifier param = programFactory.createIdentifier("arg" + counter);
            parameters.add(programFactory.createParameterDeclaration(typeRef, param));
            counter++;
        }

        //
        // actually create the declaration
        MethodDeclaration methodDecl = programFactory.createMethodDeclaration(prefix, returnTypeRef, methodName, parameters, _throws);

        //
        // the method arguments
        counter = 1;
        ASTList<Expression> args = new ASTArrayList<Expression>(localSign.size());
        for (Type type : localSign) {
            Identifier id = programFactory.createIdentifier("arg" + counter);
            VariableReference varRef = programFactory.createVariableReference(id);
            TypeReference tyRef = TypeKit.createTypeReference(programFactory, type);
            TypeCast cast = programFactory.createTypeCast(varRef, tyRef);
            args.add(cast);
            counter++;
        }

        //
        // create the methodCall
        MethodReference methodCall = programFactory.createMethodReference(programFactory.createThisReference(), methodName.deepClone(),
                args);

        // if there is a return type, make a return
        ASTList<Statement> stm = new ASTArrayList<Statement>(1);
        if (returnType != null)
            stm.add(programFactory.createReturn(methodCall));
        else
            stm.add(methodCall);

        StatementBlock block = programFactory.createStatementBlock(stm);
        methodDecl.setBody(block);

        //
        // add a comment
        methodDecl.setComments(new ASTArrayList<Comment>());
        SingleLineComment slc = getProgramFactory().createSingleLineComment("//--- This method has been created due to generics removal");
        // sould be done elsewhere methodDecl.getFirstElement().setRelativePosition(new SourceElement.Position(1, 0));
        slc.setPrefixed(true);
        methodDecl.getComments().add(slc);
        methodDecl.makeAllParentRolesValid();
        
        //
        // copy the new method to the list of methodsToAdd
        methodsToAdd.add(methodDecl);
        signaturesToAdd.add(superSig);
        debugOut("Method added", methodDecl.toSource());
    }

    private ASTList<DeclarationSpecifier> getDeclarationSpecifiers(Method origMethod) {
        ASTList<DeclarationSpecifier> ret = new ASTArrayList<DeclarationSpecifier>();
        ProgramFactory programFactory = getProgramFactory();
        if (origMethod.isFinal())
            ret.add(programFactory.createFinal());

        if (origMethod.isPrivate())
            ret.add(programFactory.createPrivate());

        if (origMethod.isProtected())
            ret.add(programFactory.createProtected());

        if (origMethod.isPublic())
            ret.add(programFactory.createPublic());

        if (origMethod.isFinal())
            ret.add(programFactory.createFinal());

        return ret;
    }

    /**
     * given a list of classtypes create throws clause out of them
     * 
     * @param exceptions
     *            a list of exception
     * @return a newly created throws-clause, or null if either null exceptions
     *         or empty list
     */
    private Throws createThrows(List<ClassType> exceptions) {

        if (exceptions == null || exceptions.isEmpty())
            return null;

        ASTList<TypeReference> tr = new ASTArrayList<TypeReference>(exceptions.size());

        for (ClassType exc : exceptions) {
            tr.add(TypeKit.createTypeReference(getProgramFactory(), exc));
        }

        return getProgramFactory().createThrows(tr);
    }

    private List<Type> getUngenericSignature(List<Type> signature) {

        List<Type> newSignature = new ArrayList<Type>(signature.size());

        for (Type type : signature) {
            newSignature.add(targetType(type));
        }

        return newSignature;
    }

    private List<Method> getOverriddenMethods(Method method) {
        SourceInfo sourceInfo = getSourceInfo();

        ClassType classType = sourceInfo.getContainingClassType(method);
        List<Type> signature = method.getSignature();
        String name = method.getName();

        List<Method> superMethods = new LinkedList<Method>();

        for (ClassType superType : sourceInfo.getSupertypes(classType)) {
            List<Method> matchingMethods = sourceInfo.getMethods(superType, name, signature, null, classType);
            if (matchingMethods.size() == 1) {
                Method match = matchingMethods.get(0);
                superMethods.add(match);
            }
        }

        return superMethods;
    }

    @Override
    public void transform() {

        if (declaration instanceof ClassDeclaration) {
            ((ClassDeclaration) declaration).setTypeParameters(null);
        } else {
            ((InterfaceDeclaration) declaration).setTypeParameters(null);
        }

        for (MethodDeclaration methodDecl : methodsToAdd) {
            attach(methodDecl, declaration, 0);
        }

    }

}