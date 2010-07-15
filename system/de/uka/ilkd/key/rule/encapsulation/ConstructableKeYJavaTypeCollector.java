// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ConstructorCall;
import de.uka.ilkd.key.rule.metaconstruct.MethodCall;
import de.uka.ilkd.key.rule.metaconstruct.ProgramMetaConstruct;
import de.uka.ilkd.key.rule.soundness.ProgramSVProxy;
import de.uka.ilkd.key.rule.soundness.ProgramSVSkolem;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.Debug;

/**
 * Collects all KeYJavaTypes that can be constructed in the run of
 * the given program.
 * <p>
 * Used when applying a Method Contract, because the user should not
 * have to (and cannot) specify the implicit fields of classes and
 * objects (&lt;next_to_create&gt; etc.) in the modifier set of the method.
 * <p>
 * The main part of the code was copied & pasted from the
 * TypeSchemeConstraintExtractor
 * 
 * @author jseidel
 * @see de.uka.ilkd.key.rule.UseOperationContractRule#apply(de.uka.ilkd.key.proof.Goal, de.uka.ilkd.key.java.Services, de.uka.ilkd.key.rule.RuleApp)
 * @see TypeSchemeConstraintExtractor
 */

public class ConstructableKeYJavaTypeCollector implements Visitor {

    //-------------------------------------------------------------------------
    //member variables
    //-------------------------------------------------------------------------
    
    /**
     * Name used for variables which are introduced as a replacement
     * for more complex expressions which cannot be handled as
     * receivers or parameters by the MethodCall and ConstructorCall
     * metaconstructs.
     */
    private static final ProgramElementName INVISIBLE_NAME
                = new ProgramElementName("invisible_var");
    
    /**
     * Map containing the formal result variables defined so far.
     */
    private final Map<MethodReference, ProgramVariable> formalResultVars
                = new HashMap<MethodReference, ProgramVariable>();

    /**
     * The services object.
     */
    private final Services services;
     
    /**
     * The methods covered so far.
     */
    private ImmutableList<ProgramMethod> coveredMethods;

    /**
     * The KeYJavaTypes found to be constructable
     */
    private ImmutableList<KeYJavaType> constructableKeYJavaTypes;
     
    /**
     * The sv instantiations, including an execution context suitable for 
     * the currently visited method.
     */
    private SVInstantiations svInst;   

    /**
     * The last error message in case of failure.
     */
    private String errorString;

    /**
     * Used by walk() to signal to the visitor methods whether the node is 
     * being entered or left.
     */
    private boolean entering;
    
    /**
     * Used by the visitor methods to let walk() descend into something other 
     * than the node's regular children.
     */
    private ProgramElement[] adoptedChildren;

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public ConstructableKeYJavaTypeCollector(Services services) {
        this.services = services;
    }
    
    
    private String addSpaces(String s) {
        while(s.length() < 45) {
             s += " ";
        }
        return s;
    }


    private boolean areInSameFamily(MethodReference mr1, MethodReference mr2) {
        ExecutionContext ec = svInst.getExecutionContext();
        
        if(!mr1.getProgramElementName().equals(mr2.getProgramElementName())) {
            return false;
        }
        
        if(!haveCommonSupertype(mr1.determineStaticPrefixType(services, ec),
                                mr2.determineStaticPrefixType(services, ec))) {
            return false;                                        
        }
        
        ImmutableList<KeYJavaType> sig1 = mr1.getMethodSignature(services, ec);
        ImmutableList<KeYJavaType> sig2 = mr2.getMethodSignature(services, ec);
        if(sig1.size() != sig2.size()) {
            return false;
        }
        
        Iterator<KeYJavaType> it1 = sig1.iterator();
        Iterator<KeYJavaType> it2 = sig2.iterator();
        while(it1.hasNext()) {
            if(!haveCommonSupertype(it1.next(), it2.next())) {
                return false;
            }
        }

        return true;
    }
    
    
    
    //-------------------------------------------------------------------------
    //helper methods
    //-------------------------------------------------------------------------
    
    /**
     * Collects all KeYJavaTypes that can be constructed in the run of
     * the given program
     * @param root the program, typically a ProgramMethod
     * @param svInst sv instantiations
     * @return a list of KeYJavaType containing all the types which might
     * be constructed.
     */
    public ImmutableList<KeYJavaType> collect(ProgramElement root, 
                                     SVInstantiations svInst) {
        //initialise members
        formalResultVars.clear();
        coveredMethods             = ImmutableSLList.<ProgramMethod>nil();
        this.svInst                = svInst;
        errorString                = null;
        constructableKeYJavaTypes  = ImmutableSLList.<KeYJavaType>nil();


        //walk the program, thereby collecting constructable types
        walk(root);

        //in case of failure, repeat the reason
        // TODO: maybe an unexpectedNodeException would be more apropriate, or even just gracefully ignoring them?
        if(errorString != null) {
            verbose("Collecting constructable KeYJavaTypes failed:");
            verbose(errorString);
        }
        
        //return the constraints
        return constructableKeYJavaTypes;
    }
    

    /**
     * Marks the current run as failed. Ensures that the resulting constraints
     * cannot be fulfilled.
     */
    private void fail(String s) {
        verbose(s);
        errorString = s;
    }


    private void failUnexpected(ProgramElement pe) {
        fail("Encountered an unexpected type of program element: " + pe
             + " (" + pe.getClass() + ")");
    }


    /**
     * Returns a list of the methods which have been analysed in the last run 
     * of extract().
     */
    public ImmutableList<ProgramMethod> getCoveredMethods() {
        return coveredMethods;
    }


    private ProgramVariable getFormalResultVar(MethodReference mr) {

        for (Object o : formalResultVars.keySet()) {
            MethodReference mr2 = (MethodReference) o;
            if (areInSameFamily(mr, mr2)) {
                return (ProgramVariable) formalResultVars.get(mr2);
            }
        }
    
        KeYJavaType resultType
                        = mr.getKeYJavaType(services,
                                            svInst.getExecutionContext());
        ProgramElementName resultName
                        = new ProgramElementName("res_" + mr.getName());
        ProgramVariable formalResultVar = new LocationVariable(resultName,
                                                              resultType);
        formalResultVars.put(mr, formalResultVar);

        return formalResultVar;
    }


    private boolean haveCommonSupertype(KeYJavaType kjt1, KeYJavaType kjt2) {
        JavaInfo javaInfo = services.getJavaInfo();
        
        if(kjt1.equals(kjt2)) {
            return true;
        }
        
        if(kjt1.getSort() instanceof PrimitiveSort
           || kjt2.getSort() instanceof PrimitiveSort) {
            return false;
        }
        
        ImmutableList<KeYJavaType> supertypes1 = javaInfo.getAllSupertypes(kjt1);
        supertypes1 = supertypes1.prepend(kjt1);
        ImmutableList<KeYJavaType> supertypes2 = javaInfo.getAllSupertypes(kjt2);
        supertypes2 = supertypes2.prepend(kjt2);

        for (KeYJavaType aSupertypes1 : supertypes1) {
            if (supertypes2.contains(aSupertypes1)) {
                return true;
            }
        }
        
        return false;
    }
    

    /**
     * Tells whether a program method should actually have a (non-empty)
     * implementation, but it is not available to KeY.
     */
    private boolean implementationIsUnavailable(ProgramMethod pm) {
        final TypeDeclaration typeDecl
                        = (TypeDeclaration) pm.getContainerType()
                                              .getJavaType();
        //pessimistically treat any library method with an empty body
        //as one with missing implementation, but make an exception for
        //those in java.lang.Object (because e.g. Object.<init>() is always
        //called during any object creation, and because they're harmless)
        return(typeDecl.isLibraryClass()
               && pm.getBody().isEmpty()
               && !typeDecl.getFullName().equals("java.lang.Object"));
    }
    
    
    public void performActionOnAbstractProgramElement(
                                                    AbstractProgramElement x) {
        failUnexpected(x);
    }


    public void performActionOnArrayDeclaration(ArrayDeclaration x) {
        failUnexpected(x);
    }


    public void performActionOnArrayInitializer(ArrayInitializer x) {
        //nothing to do (handled in performActionOnNewArray() and
        //performActionOnVariableSpecification())
    }


    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
        performActionOnPrimitiveLiteral();
    }
    
    
    
    //-------------------------------------------------------------------------
    //AST walking methods
    //-------------------------------------------------------------------------
    
    public void performActionOnArrayReference(ArrayReference x) {
        //nothing to do
    }
    
    
    public void performActionOnAssert(Assert assert1) {        
        //nothing to do        
    }


    public void performActionOnBinaryAnd(BinaryAnd x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryNot(BinaryNot x) {
        performActionOnPrimitiveBinary();
    }
    

    //-------------------------------------------------------------------------
    // the rest of the visitor interface, which is not needed at all
    //-------------------------------------------------------------------------
    
   public void performActionOnBinaryOr(BinaryOr x) {
    performActionOnPrimitiveBinary();
}


    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
     
    public void performActionOnBinaryXOr(BinaryXOr x) {
        performActionOnPrimitiveBinary();
    }

      
    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
        performActionOnPrimitiveBinary();
    }
    
   
    public void performActionOnBooleanLiteral(BooleanLiteral x) {
        performActionOnPrimitiveLiteral();
    }
    
    
    public void performActionOnBreak(Break x) {
        //nothing to do
    }
    
    public void performActionOnCase(Case x) {
        //nothing to do
    }

    
    public void performActionOnCatch(Catch x) {
        //nothing to do
    }
    
    
    public void performActionOnCatchAllStatement(CatchAllStatement x) {
        failUnexpected(x);
    }

    
    public void performActionOnCharLiteral(CharLiteral x) {
        performActionOnPrimitiveLiteral();
    }

    
    public void performActionOnClassDeclaration(ClassDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnClassInitializer(ClassInitializer x) {
        failUnexpected(x);
    }

    
    public void performActionOnComment(Comment x) {
        //nothing to do
    }

    
    public void performActionOnCompilationUnit(CompilationUnit x) {
        failUnexpected(x);
    }

    
    public void performActionOnConditional(Conditional x) {
        //nothing to do
    }
    
         
    public void performActionOnConstructorDeclaration(
                                                ConstructorDeclaration x) {
        failUnexpected(x);
    }

     
    public void performActionOnContextStatementBlock(ContextStatementBlock x) {
        failUnexpected(x);
    }

     
    public void performActionOnContinue(Continue x) {
        //nothing to do
    }

    
    public void performActionOnCopyAssignment(CopyAssignment x) {
        //nothing to do
    }

     
    public void performActionOnDefault(Default x) {
        //nothing to do
    }

    
    public void performActionOnDivide(Divide x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnDivideAssignment(DivideAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnDo(Do x) {
        //nothing to do
    }

    
    public void performActionOnDoubleLiteral(DoubleLiteral x) {
        performActionOnPrimitiveLiteral();
    }

    
    public void performActionOnElse(Else x) {
        //nothing to do
    }

    
    public void performActionOnEmptyStatement(EmptyStatement x) {
        //nothing to do
    }

    
    public void performActionOnEnhancedFor(EnhancedFor x) {
    	// nothing to do
    	
    }

     
    public void performActionOnEquals(Equals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnExactInstanceof(ExactInstanceof x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnExecutionContext(ExecutionContext x) {
        failUnexpected(x);
    }

    
    public void performActionOnExtends(Extends x) {
        failUnexpected(x);
    }

    
    public void performActionOnFieldDeclaration(FieldDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnFieldReference(FieldReference x) {
        //nothing to do
    }

    
    public void performActionOnFieldSpecification(FieldSpecification x) {
        failUnexpected(x);
    }

     
    public void performActionOnFinally(Finally x) {
        //nothing to do
    }

    
    public void performActionOnFloatLiteral(FloatLiteral x) {
        performActionOnPrimitiveLiteral();
    }
    

    public void performActionOnFor(For x) {
        //nothing to do
    }
    
    
    public void performActionOnForUpdates(ForUpdates x) {
        //nothing to do
    }
    

    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
        performActionOnPrimitiveBinary();
    }
    

    public void performActionOnGreaterThan(GreaterThan x) {
        performActionOnPrimitiveBinary();
    }
    

    public void performActionOnGuard(Guard x) {
        //nothing to do
    }

    
    public void performActionOnIf(If x) {
        //nothing to do
    }

    
    public void performActionOnImplements(Implements x) {
        failUnexpected(x);
    }

    
    public void performActionOnImplicitFieldSpecification(
                                                ImplicitFieldSpecification x) {
        failUnexpected(x);
    }

     
    public void performActionOnImport(Import x) {
        failUnexpected(x);
    }

     
    public void performActionOnInstanceof(Instanceof x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnInterfaceDeclaration(InterfaceDeclaration x) {
        failUnexpected(x);
    }

     
    public void performActionOnIntLiteral(IntLiteral x) {
        performActionOnPrimitiveLiteral();
    }


    public void performActionOnIProgramVariable(IProgramVariable x) {
        //nothing to do
    }

     
    public void performActionOnLabeledStatement(LabeledStatement x) {
        //nothing to do
    }

    
    public void performActionOnLessOrEquals(LessOrEquals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnLessThan(LessThan x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnLocalVariableDeclaration(
                                                LocalVariableDeclaration x) {
        //nothing to do (initialisation handled in
        //performActionOnVariableSpecification)
    }

    
    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }

     
    public void performActionOnLogicalAnd(LogicalAnd x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnLogicalNot(LogicalNot x) {
        performActionOnPrimitiveUnary();
    }
    
    
    public void performActionOnLogicalOr(LogicalOr x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnLongLiteral(LongLiteral x) {
        performActionOnPrimitiveLiteral();
    }

    
    public void performActionOnLoopInit(LoopInit x) {
        //nothing to do
    }

    
    public void performActionOnLoopInvariant(LoopInvariant x) {
    	// TODO resolve
    	
    }

    
    public void performActionOnMemoryAreaEC(MemoryAreaEC x) {
            failUnexpected(x);
        
    }

    
    public void performActionOnMetaClassReference(MetaClassReference x) {
        failUnexpected(x);
    }

    
    public void performActionOnMethod(ProgramMethod x) {
        failUnexpected(x);
    }

    
    /**
     * Recursively walks through the body of the encountered method
     */
    public void performActionOnMethodBodyStatement(MethodBodyStatement x) {
        if(entering) {
            //don't descend into anything - receiver and parameters have 
	    //already been visited before entering the enclosing statement
            //block
            adoptedChildren = new ProgramElement[0];
        } else {
            final ProgramMethod pm = x.getProgramMethod(services);
            final StatementBlock body = pm.getBody();
            
            //check for methods which cannot be handled
            if(implementationIsUnavailable(pm)) {
                fail("Encountered library method with unavailable "
                     + "implementation: " + pm);
            }
            if(pm.isNative()) {
                fail("Encountered native method: " + pm);
            }

            //go down into method, if not already covered
            if(!coveredMethods.contains(pm)) {
                coveredMethods = coveredMethods.append(pm);
                
                //determine new execution context
                final TypeReference classContext 
                                = new TypeRef(pm.getContainerType());
                final ReferencePrefix runtimeInstance 
                                = x.getDesignatedContext();
                
                
                
                final ExecutionContext executionContext 
		    = new ExecutionContext(classContext, null,runtimeInstance == null ? null : 
			new RuntimeInstanceEC(runtimeInstance));
                                                       
                //save context information
                final SVInstantiations oldSvInst 
                                = svInst;
                
                //adapt context information
                svInst                     = svInst.replace(null, 
                                                            null,
                                                            executionContext, 
                                                            body);
                
                //walk the body
                verbose("=========body enter (" + pm + ")=========");
                walk(body);
                verbose("=========body exit (" + pm + ")==========");
                
                svInst                     = oldSvInst;
            }

        }
    }

    
    public void performActionOnMethodDeclaration(MethodDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnMethodFrame(MethodFrame x) {
        failUnexpected(x);
    }

    
    /**
     * Symbolically executes the MethodReference and adopts the
     * corresponding ProgramElement, so the newly created       
     * MethodBodyStatements can be visited. 
     */
    public void performActionOnMethodReference(MethodReference x) {
        if(entering) {
            //try to get the method's result type
            final KeYJavaType resultType 
                               = x.getKeYJavaType(services, 
                                                  svInst.getExecutionContext());


            //if the method is non-void, create a result variable and save
            //it in an SVInstantiations as instantiation of some SV
            final MethodReference simpleX = simplifyMethodReference(x);      
            final ProgramVariable formalResultVar;
            final SchemaVariable formalResultSV;
            final SVInstantiations mySvInst;
            if(resultType != null) {
                formalResultVar = getFormalResultVar(simpleX);
                formalResultSV
                        = new NameSV(formalResultVar.getProgramElementName()
                                     + "SV");
                mySvInst = svInst.add(formalResultSV, formalResultVar);
            } else {
                formalResultVar = null;
                formalResultSV = null;
                mySvInst = svInst;
            }

            //let the MethodCall metaconstruct expand the method reference
            final MethodCall mc = new MethodCall(formalResultSV, simpleX);
            final ProgramElement expandedPe = mc.symbolicExecution(simpleX,
                                                                   services, 
                                                                   mySvInst);


                                                                   
            //descend into prefix, parameters and expansion instead of
            //normal children
            final ReferencePrefix rp = x.getReferencePrefix();
            final ImmutableArray<Expression> args = x.getArguments();
            adoptedChildren = new ProgramElement[args.size() + 2];
            adoptedChildren[0] = (rp instanceof Expression
                                  ? rp
                                  : new ThisReference());
            for(int i = 0; i < args.size(); i++) {
                adoptedChildren[i + 1] = args.get(i);
            }
            adoptedChildren[args.size() + 1] = expandedPe;
        }
    }

    
    public void performActionOnMinus(Minus x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnMinusAssignment(MinusAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnModifier(Modifier x) {
        failUnexpected(x);
    }

    
    public void performActionOnModulo(Modulo x) {
        performActionOnPrimitiveBinary();
    }
    

    public void performActionOnModuloAssignment(ModuloAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnNegative(Negative x) {
        performActionOnPrimitiveUnary();
    }

    
    /**
     * Collects the KeYJavaType, transforms the constructor into normal form
     * and recursively walks it.
     */
    public void performActionOnNew(New x) {
        if(entering) {
            //get the new-object type
            KeYJavaType newObjectType
                              = x.getKeYJavaType(services, 
                                                 svInst.getExecutionContext());
            assert newObjectType != null;

	    if( !constructableKeYJavaTypes.contains( newObjectType ) )
		constructableKeYJavaTypes = constructableKeYJavaTypes.prepend( newObjectType );

            //create a new-object variable and save it in an SVInstantiations
            //as instantiation of some SV
            ProgramElementName newObjectName
                     = new ProgramElementName("new" + newObjectType.getSort()
                                                                   .name());
            ProgramVariable newObjectVar
                        = new LocationVariable(newObjectName, newObjectType);
            SchemaVariable newObjectSV = new NameSV(newObjectName + "SV");
            SVInstantiations mySvInst = svInst.add(newObjectSV, newObjectVar);

            //let the ConstructorCall metaconstruct expand the constructor 
            //reference
	    New simpleX = simplifyNew(x);
            ConstructorCall cc = new ConstructorCall(newObjectSV, simpleX);
            ProgramElement expandedPe = cc.symbolicExecution(simpleX,
                                                             services,
                                                             mySvInst);

            //descend into prefix, parameters and expansion instead of
            //normal children
            final ImmutableArray<Expression> args = x.getArguments();
            adoptedChildren = new ProgramElement[args.size() + 2];
            adoptedChildren[0] = new ThisReference();
            for(int i = 0; i < args.size(); i++) {
                adoptedChildren[i + 1] = args.get(i);
            }
            adoptedChildren[args.size() + 1] = expandedPe;

        } else {
	}
    }

    
    public void performActionOnNewArray(NewArray x) {
        //nothing to do
    }

    
    public void performActionOnNotEquals(NotEquals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnNullLiteral(NullLiteral x) {
        //nothing to do
    }
        
    
    public void performActionOnPackageReference(PackageReference x) {
        //nothing to do
    }

    
    public void performActionOnPackageSpecification(PackageSpecification x) {
        failUnexpected(x);
    }

    
    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
        //nothing to do
    }

    
    public void performActionOnParenthesizedExpression(
                                                    ParenthesizedExpression x) {
        //nothing to do
    }

    
    public void performActionOnPassiveExpression(PassiveExpression x) {
        //nothing to do
    }

    
    public void performActionOnPlus(Plus x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnPlusAssignment(PlusAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnPositive(Positive x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnPostDecrement(PostDecrement x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnPostIncrement(PostIncrement x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnPreDecrement(PreDecrement x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnPreIncrement(PreIncrement x) {
        performActionOnPrimitiveUnary();
    }

     
    private void performActionOnPrimitiveBinary() {
        //nothing to do
    }

    
    private void performActionOnPrimitiveLiteral() {
            //nothing to do
        }

    
    private void performActionOnPrimitiveUnary() {
        //nothing to do
    }

     
    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);        
    }

    
    public void performActionOnProgramElementName(ProgramElementName x) {
        //nothing to do
    }

    
    public void performActionOnProgramMetaConstruct(ProgramMetaConstruct x) {
        failUnexpected(x);
    }

    
    public void performActionOnProgramMethod(ProgramMethod x) {
        failUnexpected(x);
    }

     
    public void performActionOnProgramSVProxy(ProgramSVProxy x) {
        failUnexpected(x);
    }

    
    public void performActionOnProgramSVSkolem(ProgramSVSkolem x) {
        failUnexpected(x);
    }

    
    public void performActionOnProgramVariable(ProgramVariable x) {
        //nothing to do
    }

    
    public void performActionOnReturn(Return x) {
        //nothing to do
    }

    
    public void performActionOnRuntimeInstanceEC(RuntimeInstanceEC x) {
            failUnexpected(x);	    
    }

     
    public void performActionOnSchematicFieldReference(
                                                    SchematicFieldReference x) {
        failUnexpected(x);
    }

    
    public void performActionOnSchemaVariable(SchemaVariable x) {
        failUnexpected((ProgramSV) x);
    }

    
    public void performActionOnSetAssignment(SetAssignment x) {
    	// TODO resolve
    	
    }

    
    public void performActionOnShiftLeft(ShiftLeft x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnShiftRight(ShiftRight x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnStatementBlock(StatementBlock x) {
        //nothing to do
    }

    
    public void performActionOnStringLiteral(StringLiteral x) {
        //nothing to do
    }

    
    public void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnSuperConstructorReference(
                                                SuperConstructorReference x) {
        //never met, because ConstructorCall replaces it with
        //ordinary MethodReference
        failUnexpected(x); 
    }

    
    public void performActionOnSuperReference(SuperReference x) {
        //nothing to do
    }
    

    public void performActionOnSwitch(Switch x) {
        //nothing to do
    }

    
    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
        //nothing to do
    }

    
    public void performActionOnThen(Then x) {
        //nothing to do
    }

    
    public void performActionOnThisConstructorReference(
                                                ThisConstructorReference x) {
        //never met, because ConstructorCall replaces it with
        //ordinary MethodReference
        failUnexpected(x);
    }

     
    public void performActionOnThisReference(ThisReference x) {
        //nothing to do
    }

    
    public void performActionOnThrow(Throw x) {
        //nothing to do
    }

    
    public void performActionOnThrows(Throws x) {
        //nothing to do
    }

    
    public void performActionOnTimes(Times x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnTimesAssignment(TimesAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnTry(Try x) {
        //nothing to do
    }

    
    public void performActionOnTypeCast(TypeCast x) {
        //nothing to do
    }

    
    public void performActionOnTypeReference(TypeReference x) {
        //nothing to do
    }

    
    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnUnsignedShiftRightAssignment(
                                            UnsignedShiftRightAssignment x) {
        performActionOnPrimitiveBinary();
    }
  
    public void performActionOnVariableDeclaration(VariableDeclaration x) {
        failUnexpected(x);
    }
    
    public void performActionOnVariableReference(VariableReference x) {
        //nothing to do
    }
    

    public void performActionOnVariableSpecification(VariableSpecification x) {
        //nothing to do
    }


    public void performActionOnWhile(While x) {
        //nothing to do
    }


    /**
     * Replaces an expression by a simpler one with the same static type,
     * so that it can be handled as a receiver or parameter by the
     * ConstructorCall and MethodCall metaconstructs.
     */
    private ProgramVariable simplifyExpression(Expression expression) {
        KeYJavaType staticKjt
                = expression.getKeYJavaType(services,
                                            svInst.getExecutionContext());
        Debug.assertTrue(staticKjt != null);
        return new LocationVariable(INVISIBLE_NAME, staticKjt);
    }


	private ImmutableArray<Expression> simplifyExpressions(ImmutableArray<Expression> expressions) {
        Expression[] result = new Expression[expressions.size()];
        for(int i = 0; i < expressions.size(); i++) {
            result[i] = simplifyExpression(expressions.get(i));
        }
        return new ImmutableArray<Expression>(result);
        }


	private MethodReference simplifyMethodReference(MethodReference mr) {
            ReferencePrefix rp = mr.getReferencePrefix();
        ReferencePrefix simpleRp = (rp instanceof ThisReference
                                        || rp instanceof SuperReference
                                        || rp instanceof ProgramVariable
                                        || rp instanceof FieldReference
                                        || !(rp instanceof Expression)
                                        ? rp
                                        : simplifyExpression((Expression) rp));

            return new MethodReference(simplifyExpressions(mr.getArguments()), 
        			   mr.getMethodName(), 
        			   simpleRp);
        }


	private New simplifyNew(New n) {
            Debug.assertFalse(n.getReferencePrefix() instanceof Expression);
        ImmutableArray<Expression> simpleArgs = simplifyExpressions(n.getArguments());
        Expression[] simpleArgsArray = new Expression[simpleArgs.size()];
        for(int i = 0; i < simpleArgs.size(); i++) {
            simpleArgsArray[i] = simpleArgs.get(i);
        }
        return new New(simpleArgsArray, 
        	       n.getTypeReference(), 
        	       n.getReferencePrefix());
        }


	private void verbose(Object o) {
            //System.out.println(o);
        }


	protected void walk(ProgramElement node) {
            //debug output
            String fullClassName = node.getClass().getName();
            String className
                    = fullClassName.substring(fullClassName.lastIndexOf(".") + 1);
            String enteringString
                    = addSpaces("Entering:   " + node) + "(" + className + ")";
            String ascendingString
                    = addSpaces("Ascending:  " + node) + "(" + className + ")";
            verbose(enteringString);
        
            //visit the node
            adoptedChildren = null;
            entering = true;
            node.visit(this);
            
            //walk children (either the adopted or the normal ones)
            if(adoptedChildren != null) {
                ProgramElement[] ac = adoptedChildren.clone();
                for (ProgramElement anAc : ac) {
                    walk(anAc);
                }
                verbose(ascendingString);
            } else if(node instanceof NonTerminalProgramElement) {
                NonTerminalProgramElement nonTerminalNode 
                            = (NonTerminalProgramElement) node;
                for(int i = 0; i < nonTerminalNode.getChildCount(); i++) {
                    walk(nonTerminalNode.getChildAt(i));
                }
                verbose(ascendingString);
            }
            
            //visit the node again
            entering = false;
            node.visit(this);
        }


  
}
