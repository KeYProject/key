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

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.abstraction.TypeParameter;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.Reference;
import recoder.java.StatementContainer;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.expression.Assignment;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.NameReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Return;
import recoder.kit.ProblemReport;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTList;
import recoder.service.SourceInfo;

public class ResolveMemberReference extends GenericResolutionTransformation {

    private NameReference reference;

    private TypeReference typeToReference;

    public ResolveMemberReference(NameReference reference, CrossReferenceServiceConfiguration sc) {
        super(sc);
        this.reference = reference;
    }

    /**
     * Analys a MemberReference.
     * 
     * Considering the following example:
     * 
     * <pre>
     * class B ...
     * class G&lt;E&gt; { E m() {...} }
     * 
     * ... 
     * G&lt;B&gt; g = new G&lt;B&gt;(); 
     * B b = g.m();
     * ... 
     * </pre>
     * 
     * The reference <code>g.m()</code> is the one under test. Several types
     * will show up:
     * <ul>
     * <li><code>declarationType</code> - the type of the member at its
     * declaration. Here the type of <code>G.m()</code> which is
     * <code>E</code>.</li>
     * <li><code>genericFreeDeclaraionType</code> - the type of the
     * declaration in a non-generic situation, which is
     * <code>java.lang.Object</code> here.</li>
     * <li><code>kernelType</code> - if declarationType is an array,
     * kernelType will be the component type (with all [] removed)</li>
     * <li><code>actualType</code> - the type of the member in the
     * parameterized instance: here the type of <code>G&lt;B&gt;.m()</code>
     * which is <code>B</code>.</li>
     * <li><code>genericFreeType</code> - if the actualType is a TV itsself,
     * this is the type that it will be replaced in a non-generic situation (<code>Object</code>
     * or first boundary).</li>
     * <li><code>resolvedType</code> - if there are multiple bounds the
     * reference might have to be cast to a different one than the first.</li>
     * </ul>
     * 
     * Also, if there are explicit type parameters, they will be removed.
     */
    @Override
    public ProblemReport analyze() {

        setProblemReport(IDENTITY);

        // we have to transform if there are explicit type arguments.
        if (reference instanceof MethodReference) {
            MethodReference methRef = (MethodReference) reference;
            ASTList<TypeArgumentDeclaration> typeArguments = methRef.getTypeArguments();
            if (typeArguments != null && typeArguments.size() > 0)
                setProblemReport(EQUIVALENCE);
        }

        SourceInfo sourceInfo = getSourceInfo();
        ProgramFactory programFactory = getServiceConfiguration().getProgramFactory();

        // thats the type of the declaration
        Type declarationType = getFormalType();

        // kernelType = formalType with [][]...[] stripped
        Type kernelType = declarationType;
        while (kernelType instanceof ArrayType) {
            kernelType = ((ArrayType) kernelType).getBaseType();
        }

        NonTerminalProgramElement parent = reference.getASTParent();
        boolean isTypeParameter = kernelType instanceof TypeParameter;
        boolean isStatement = parent instanceof StatementContainer;
        boolean isLHS = isLHS(reference);

        // a cast might have to be introduced if the type is a type parameter
        // and the expression is not used as a statement or a lhs in an
        // assignment.
        if (isTypeParameter && !isStatement && !isLHS) {
            // that's the type for this instantation
            // not of the declaration
            // (ths may be another Typevar)
            Type actualType = sourceInfo.getType(reference);

            // that's the generic-free version of actualType
            Type genericfreeType = targetType(actualType);

            // that's the type that the reference's declaration has after
            // de-generification
            Type genericFreeDeclarationType = targetType(declarationType);

            // that's the type that is really needed here
            Type resolvedType = resolveType();

            // show all types
            debugOut("actualType", actualType.getFullName());
            debugOut("genericfreeType", genericfreeType.getFullName());
            debugOut("resolvedType", resolvedType.getFullName());
            debugOut("declarationType", declarationType.getFullName());
            debugOut("genericFreeDeclarationType", genericFreeDeclarationType.getFullName());

            ClassType javaLangObject = getNameInfo().getJavaLangObject();
            // the cast is unnecessary if the formal type is already the
            // targettype. Cast to j.l.Object is unecessary
            // (types are == comparable, I hope)
            if (resolvedType != genericFreeDeclarationType && resolvedType != javaLangObject) {
                typeToReference = TypeKit.createTypeReference(programFactory, resolvedType);
                setProblemReport(EQUIVALENCE);
            }
        }

        return getProblemReport();
    }

    /**
     * return true iff the reference is a lhs of an assignment: Either an
     * assignment operator or ???.
     * 
     * @todo
     * 
     * @param reference
     * @return true iff the reference is a lhs of an assignment: Either an
     * assignment operator or ???.
     *  
     */
    private static boolean isLHS(Reference reference) {
        NonTerminalProgramElement parent = reference.getASTParent();
        if (parent instanceof Assignment) {
            Assignment ass = (Assignment) parent;
            return ass.getExpressionAt(0) == reference;
        } // else if

        return false;
    }

    /**
     * get the static type of the the declaration of the member. This might be a
     * type variable even if the type instantiation does not have type variables
     * 
     * @return the type of the the declaration of the referenced member
     */
    private Type getFormalType() {

        SourceInfo sourceInfo = getSourceInfo();
        Type formalType = null;

        if (reference instanceof MethodReference) {
            MethodReference methodReference = (MethodReference) reference;
            formalType = sourceInfo.getMethod(methodReference).getReturnType();
        } else if (reference instanceof FieldReference) {
            FieldReference fieldReference = (FieldReference) reference;
            formalType = sourceInfo.getField(fieldReference).getType();
        } else if (reference instanceof VariableReference) {
            VariableReference variableReference = (VariableReference) reference;
            formalType = sourceInfo.getVariable(variableReference).getType();
        }
        return formalType;
    }

    /**
     * Problem:
     * 
     * <code>
     * interface B { void bb(); }
     * interface C {}
     * 
     * class A&lt;E extends C&amp;B&gt; {
     *   E e;
     *   
     *   void _d() {
     *     e.bb();
     *   }         
     * }
     * </code>
     * 
     * would be resolved to
     * 
     * <code>
     * intfcs s. above
     * 
     * class A {
     *   C e;
     *   
     *   void _d() {
     *     ((B)e).bb();
     *   }
     * }
     * </code>
     * 
     * because the element <code>e</code> cannot have a static types C and B
     * at the same time. Such casts have to be introduced in such situations.
     * 
     * The detection is handled for the following situations:
     * <ul>
     * <li>FieldReference as suffix</li>
     * <li>MethodReference as suffix</li>
     * <li>CopyAssignments, reference as rhs.</li>
     * <li>VariableSpecifications (and field specs) (which are not
     * assignments!)</li>
     * <li>MethodReference as parameter</li>
     * </ul>
     * 
     * @todo DAS IST JA WOHL NOCH NICHT
     * 
     * @return the resolved type
     */
    private Type resolveType() {

        NonTerminalProgramElement parent = reference.getASTParent();

        if (parent instanceof MethodReference) {
            MethodReference methRef = (MethodReference) parent;
            Method meth = getSourceInfo().getMethod(methRef);
            int index = -1;
            ASTList<Expression> args = methRef.getArguments();
            if (args != null)
                index = args.indexOf(reference);
            if (index == -1) {
                // not an argument --> must be prefix
                Type classType = meth.getContainingClassType();
                return classType;
            } else {
                // it's an argument to the method
                Type argType = meth.getSignature().get(index);
                return targetType(argType);
            }
        }

        if (parent instanceof FieldReference) {
            FieldReference fieldRef = (FieldReference) parent;
            Field field = getSourceInfo().getField(fieldRef);
            Type classType = field.getContainingClassType();
            return classType;
        }

        if (parent instanceof Assignment) {
            Assignment assignment = (Assignment) parent;
            if (assignment.getChildAt(1) == reference) {
                // only rhs is relevant
                Expression lhs = assignment.getArguments().get(0);
                Type lhsType = getSourceInfo().getType(lhs);
                return targetType(lhsType);
            }
        }

        if (parent instanceof VariableSpecification) {
            VariableSpecification varSpec = (VariableSpecification) parent;
            VariableDeclaration decl = (VariableDeclaration) parent.getASTParent();
            Type varType = targetType(getSourceInfo().getType(decl.getTypeReference()));
            int dimensions = varSpec.getDimensions();
            if (dimensions > 0)
                varType = getNameInfo().createArrayType(varType, dimensions);

            return varType;
        }

        if (parent instanceof Return) {
            MethodDeclaration md = getEnclosingMethod(parent);
            return targetType(md.getReturnType());
        }

        return targetType(getSourceInfo().getType(reference));
    }

    private static MethodDeclaration getEnclosingMethod(NonTerminalProgramElement pe) {
        while (!(pe instanceof MethodDeclaration)) {
            pe = pe.getASTParent();
        }
        return (MethodDeclaration) pe;
    }

    @Override
    public void transform() {

        // remove explicit type arguments - if there are any
        if (reference instanceof MethodReference) {
            MethodReference methRef = (MethodReference) reference;
            methRef.setTypeArguments(null);
        }

        if (typeToReference != null) {
            ProgramFactory programFactory = getServiceConfiguration().getProgramFactory();
            TypeCast cast = programFactory.createTypeCast((Expression) reference.deepClone(), typeToReference);
            ParenthesizedExpression replaceWith = programFactory.createParenthesizedExpression(cast);
            if (replaceWith != null)
                replace(reference, replaceWith);
        }
    }

}