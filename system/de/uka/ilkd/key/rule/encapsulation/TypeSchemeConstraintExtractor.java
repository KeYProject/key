// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import java.util.Stack;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ConstructorCall;
import de.uka.ilkd.key.rule.metaconstruct.MethodCall;
import de.uka.ilkd.key.rule.metaconstruct.ProgramMetaConstruct;
import de.uka.ilkd.key.rule.soundness.ProgramSVProxy;
import de.uka.ilkd.key.rule.soundness.ProgramSVSkolem;
import de.uka.ilkd.key.util.Debug;


class TypeSchemeConstraintExtractor implements Visitor {

    //-------------------------------------------------------------------------
    //member variables
    //-------------------------------------------------------------------------
    
    /**
     * Constant used to mark levels on the stack.
     */
    private static final Object LEVEL = new Object() {
        public String toString() {
            return "LEVEL";
        }
    };

    /**
     * Name used for variables which are introduced as a replacement
     * for more complex expressions which cannot be handled as
     * receivers or parameters by the MethodCall and ConstructorCall
     * metaconstructs.
     */
    private static final ProgramElementName INVISIBLE_NAME
                = new ProgramElementName("invisible_var");
    
    /**
     * Stack used to propagate type scheme terms around the AST.
     */
    private final Stack /*TypeSchemeTerm*/ stack = new Stack();

    /**
     * Map containing the formal result variables defined so far.
     */
    private final Map /*MethodReference -> ProgramVariable*/ formalResultVars
                = new HashMap();

    /**
     * The services object.
     */
    private final Services services;

    /**
     * Type scheme checker.
     */
    private TypeSchemeChecker checker;
     
    /**
     * The methods covered so far.
     */
    private ListOfProgramMethod coveredMethods;
     
    /**
     * The sv instantiations, including an execution context suitable for 
     * the currently visited method.
     */
    private SVInstantiations svInst;   

    /**
     * The term of the formal result variable of the currently visited method.
     */
    private TypeSchemeTerm contextFormalResultTerm;

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

    public TypeSchemeConstraintExtractor(Services services) {
        this.services = services;
    }
    
    
    /**
     * Compares a program with the universe type rules.
     * @param root the program
     * @param annotations map from Location to TypeSchemeTerm containing
     * the predefined field annotations; fields not contained in the map are
     * taken to have type scheme rootS
     * @param svInst sv instantiations
     * @return a list of constraints describing what must hold for the program
     * to satisfy the type rules
     */
    public ListOfTypeSchemeConstraint extract(ProgramElement root, 
                                              Map annotations,
                                              SVInstantiations svInst) {
        //initialise members
        stack.clear();
        formalResultVars.clear();
        checker                    = new TypeSchemeChecker(annotations);
        coveredMethods             = SLListOfProgramMethod.EMPTY_LIST;
        this.svInst                = svInst;
        contextFormalResultTerm    = null;
        errorString                = null;
        
        //walk the program, thereby generating the constraints
        try {
            walk(root);
        } catch(Exception e) {
            fail("An exception occurred during the extraction:");
            e.printStackTrace(System.out);
            checker.fail();
            return checker.getConstraints();
        }

        //in case of failure, repeat the reason
        if(errorString != null) {
            verbose("The extraction failed because of the following problem:");
            verbose(errorString);
        }
        
        //return the constraints
        return checker.getConstraints();
    }


    /**
     * Returns a list of the methods which have been analysed in the last run 
     * of extract().
     */
    public ListOfProgramMethod getCoveredMethods() {
        return coveredMethods;
    }
    
    
    
    //-------------------------------------------------------------------------
    //helper methods
    //-------------------------------------------------------------------------
    
    private void verbose(Object o) {
        //System.out.println(o);
    }
    

    /**
     * Marks the current run as failed. Ensures that the resulting constraints
     * cannot be fulfilled.
     */
    private void fail(String s) {
        verbose(s);
        errorString = s;
        checker.fail();
    }


    private void failUnexpected(ProgramElement pe) {
        fail("Encountered an unexpected type of program element: " + pe
             + " (" + pe.getClass() + ")");
    }

    
    private void printStack() {
        verbose("Current stack:");
        Iterator it = stack.iterator();
        while(it.hasNext()) {
            verbose(it.next());
        }
    }
    
    
    /**
     * Pushes a term onto the stack.
     */
    private void push(TypeSchemeTerm term) {
        Debug.assertTrue(term != null);
        verbose("Pushing:    " + term);
        stack.push(term);
    }
    
    
    /**
     * Pops a term off the stack.
     */
    private TypeSchemeTerm pop() {
        verbose("Popping:    " + stack.peek());
        if(stack.peek() == LEVEL) {
            printStack();
        }
        return (TypeSchemeTerm) stack.pop();
    }
        
    
    /**
     * Pushes the LEVEL constant onto the stack.
     */
    private void pushLevel() {
        stack.push(LEVEL);
    }
    
    
    /**
     * Pops all elements until the next LEVEL constant (inclusive) from the 
     * stack.
     * @return a list of the elements, whose the first element is the lowermost
     * element from the stack which is not LEVEL
     */
    private ListOfTypeSchemeTerm popLevel() {
        ListOfTypeSchemeTerm result = SLListOfTypeSchemeTerm.EMPTY_LIST;
    
        Object o = stack.pop();
        while(o != LEVEL) {
            verbose("Level-popping: " + o);
            result = result.prepend((TypeSchemeTerm) o);
            o = stack.pop();
        }
        
        return result;
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
        
        ListOfKeYJavaType supertypes1 = javaInfo.getAllSupertypes(kjt1);
        supertypes1 = supertypes1.prepend(kjt1);
        ListOfKeYJavaType supertypes2 = javaInfo.getAllSupertypes(kjt2);
        supertypes2 = supertypes2.prepend(kjt2);
        
        IteratorOfKeYJavaType it = supertypes1.iterator();
        while(it.hasNext()) {
            if(supertypes2.contains(it.next())) {
                return true;
            }
        }
        
        return false;
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
        
        ListOfKeYJavaType sig1 = mr1.getMethodSignature(services, ec);
        ListOfKeYJavaType sig2 = mr2.getMethodSignature(services, ec);
        if(sig1.size() != sig2.size()) {
            return false;
        }
        
        IteratorOfKeYJavaType it1 = sig1.iterator();
        IteratorOfKeYJavaType it2 = sig2.iterator();
        while(it1.hasNext()) {
            if(!haveCommonSupertype(it1.next(), it2.next())) {
                return false;
            }
        }

        return true;
    }


    private ProgramVariable getFormalResultVar(MethodReference mr) {
        Iterator it = formalResultVars.keySet().iterator();

        while(it.hasNext()) {
            MethodReference mr2 = (MethodReference) it.next();
            if(areInSameFamily(mr, mr2)) {
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
    

    /**
     * Tells whether a method body statement describes a constructor invocation
     * within an allocation (i.e. not this() or super())
     */
    private boolean isAllocationConstructorInvocation(MethodBodyStatement mbs) {
        final ProgramMethod pm = mbs.getProgramMethod(services);
        return (pm.name().toString().endsWith(ConstructorNormalformBuilder.
                CONSTRUCTOR_NORMALFORM_IDENTIFIER) && 
                mbs.getResultVariable() == null);
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
    
    
    /**
     * Tells whether the current context is static or not.
     */
    private boolean contextIsStatic() {
        ExecutionContext executionContext = svInst.getExecutionContext();
        return (executionContext == null 
                || !(executionContext.getRuntimeInstance()
                     instanceof Expression));
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


    private ArrayOfExpression simplifyExpressions(
						ArrayOfExpression expressions) {
	Expression[] result = new Expression[expressions.size()];
	for(int i = 0; i < expressions.size(); i++) {
	    result[i] = simplifyExpression(expressions.getExpression(i));
	}
	return new ArrayOfExpression(result);
    }


    private New simplifyNew(New n) {
        Debug.assertFalse(n.getReferencePrefix() instanceof Expression);
	ArrayOfExpression simpleArgs = simplifyExpressions(n.getArguments());
	Expression[] simpleArgsArray = new Expression[simpleArgs.size()];
	for(int i = 0; i < simpleArgs.size(); i++) {
	    simpleArgsArray[i] = simpleArgs.getExpression(i);
	}
	return new New(simpleArgsArray, 
		       n.getTypeReference(), 
		       n.getReferencePrefix());
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
    
    
    
    //-------------------------------------------------------------------------
    //AST walking methods
    //-------------------------------------------------------------------------
    
    private String addSpaces(String s) {
        while(s.length() < 45) {
             s += " ";
        }
        return s;
    }
    
    
    private void walk(ProgramElement node) {
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
            ProgramElement[] ac = (ProgramElement[]) adoptedChildren.clone();
            for(int i = 0; i < ac.length; i++) {
                walk(ac[i]);
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


    private void performActionOnPrimitiveLiteral() {
        if(!entering) {
            TypeSchemeTerm resultTerm = checker.checkPrimitiveLiteral();
            push(resultTerm);
        }
    }


    private void performActionOnPrimitiveUnary() {
        if(!entering) {
            TypeSchemeTerm operandTerm = pop();
            TypeSchemeTerm resultTerm
                        = checker.checkPrimitiveUnary(operandTerm);
            push(resultTerm);
        }
    }

    
     
    private void performActionOnPrimitiveBinary() {
        if(!entering) {
            TypeSchemeTerm operandTerm1 = pop();
            TypeSchemeTerm operandTerm2 = pop();

            TypeSchemeTerm resultTerm
                        = checker.checkPrimitiveBinary(operandTerm1,
                                                       operandTerm2);

            push(resultTerm);
        }
    }

      
    public void performActionOnAbstractProgramElement(
                                                    AbstractProgramElement x) {
        failUnexpected(x);
    }
    
   
    public void performActionOnProgramElementName(ProgramElementName x) {
        //nothing to do
    }
    
    
    public void performActionOnProgramVariable(ProgramVariable x) {
        if(!entering) {
            TypeSchemeTerm varTerm;
            
            if(x.isMember()) {
                if(x.isStatic()) {
                    varTerm = checker.checkStaticField(x);
                } else {
                    varTerm = checker.checkInstanceField(x);
                }
            } else {
                if(contextIsStatic()) {
                    varTerm = checker.checkStaticLocalVariable(x);
                } else {
                    varTerm = checker.checkInstanceLocalVariable(x);
                }
            }
        
            push(varTerm);
        }
    }
    
    

    
    public void performActionOnSchemaVariable(SchemaVariable x) {
        failUnexpected((ProgramSV) x);
    }
    
    
    public void performActionOnProgramMethod(ProgramMethod x) {
        failUnexpected(x);
    }

    
    public void performActionOnProgramMetaConstruct(ProgramMetaConstruct x) {
        failUnexpected(x);
    }

    
    public void performActionOnContextStatementBlock(ContextStatementBlock x) {
        failUnexpected(x);
    }

    
    public void performActionOnIntLiteral(IntLiteral x) {
        performActionOnPrimitiveLiteral();
    }

    
    public void performActionOnBooleanLiteral(BooleanLiteral x) {
        performActionOnPrimitiveLiteral();
    }

    
    public void performActionOnStringLiteral(StringLiteral x) {
        if(!entering) {
            TypeSchemeTerm stringLiteralTerm = checker.checkStringLiteral();
            push(stringLiteralTerm);
        }
    }

    
    public void performActionOnNullLiteral(NullLiteral x) {
        if(!entering) {
            TypeSchemeTerm nullTerm = checker.checkNull();
            push(nullTerm);
        }
    }
    
         
    public void performActionOnCharLiteral(CharLiteral x) {
        performActionOnPrimitiveLiteral();
    }

     
    public void performActionOnDoubleLiteral(DoubleLiteral x) {
        performActionOnPrimitiveLiteral();
    }

     
    public void performActionOnLongLiteral(LongLiteral x) {
        performActionOnPrimitiveLiteral();
    }

    
    public void performActionOnFloatLiteral(FloatLiteral x) {
        performActionOnPrimitiveLiteral();
    }

     
    public void performActionOnPackageSpecification(PackageSpecification x) {
        failUnexpected(x);
    }

    
    public void performActionOnTypeReference(TypeReference x) {
        //nothing to do
    }

    
    public void performActionOnPackageReference(PackageReference x) {
        //nothing to do
    }

    
    public void performActionOnThrows(Throws x) {
        //nothing to do
    }

    
    public void performActionOnArrayInitializer(ArrayInitializer x) {
        //nothing to do (handled in performActionOnNewArray() and
        //performActionOnVariableSpecification())
    }

    
    public void performActionOnCompilationUnit(CompilationUnit x) {
        failUnexpected(x);
    }

    
    public void performActionOnArrayDeclaration(ArrayDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x) {
        failUnexpected(x);
    }

     
    public void performActionOnClassDeclaration(ClassDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnInterfaceDeclaration(InterfaceDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnFieldDeclaration(FieldDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnLocalVariableDeclaration(
                                                LocalVariableDeclaration x) {
        //nothing to do (initialisation handled in
        //performActionOnVariableSpecification)
    }

    
    public void performActionOnVariableDeclaration(VariableDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
        //nothing to do
    }
    
    public void performActionOnCurrentMemoryAreaReference(CurrentMemoryAreaReference x){
        //nothing to do
    }
    
    public void performActionOnMethodDeclaration(MethodDeclaration x) {
        failUnexpected(x);
    }

     
    public void performActionOnClassInitializer(ClassInitializer x) {
        failUnexpected(x);
    }

    
    public void performActionOnStatementBlock(StatementBlock x) {
        if(entering) {
            pushLevel();
        } else {
            popLevel();
        }
    }
    

    public void performActionOnBreak(Break x) {
        //nothing to do
    }
    
    
    public void performActionOnContinue(Continue x) {
        //nothing to do
    }
    

    public void performActionOnReturn(Return x) {
        if(!entering) {
            TypeSchemeTerm actualResultTerm = null;
            if(contextFormalResultTerm != null) {
                actualResultTerm = pop();
            }
            checker.checkReturn(actualResultTerm, contextFormalResultTerm);
        }
    }
    

    public void performActionOnThrow(Throw x) {
        //nothing to do
    }
    

    public void performActionOnDo(Do x) {
        //nothing to do
    }

    
    public void performActionOnFor(For x) {
        //nothing to do
    }

    
    public void performActionOnWhile(While x) {
        //nothing to do
    }

    
    public void performActionOnIf(If x) {
        //nothing to do
    }

     
    public void performActionOnSwitch(Switch x) {
        //nothing to do
    }

     
    public void performActionOnTry(Try x) {
        //nothing to do
    }

    
    public void performActionOnLabeledStatement(LabeledStatement x) {
        //nothing to do
    }

     
    public void performActionOnMethodFrame(MethodFrame x) {
        failUnexpected(x);
    }

    
    public void performActionOnMethodBodyStatement(MethodBodyStatement x) {
        if(entering) {
            //don't descend into anything - receiver and parameters have 
	    //already been visited before entering the enclosing statement
            //block
            adoptedChildren = new ProgramElement[0];
        } else {
            final ProgramMethod pm = x.getProgramMethod(services);
            final StatementBlock body = pm.getBody();
            final boolean isAllocation = isAllocationConstructorInvocation(x);
            final boolean isStatic = pm.isStatic();
            
            //check for methods which cannot be handled
            if(implementationIsUnavailable(pm)) {
                fail("Encountered library method with unavailable "
                     + "implementation: " + pm);
            }
            if(pm.isNative()) {
                fail("Encountered native method: " + pm);
            }

            //pop the level mark of the enclosing statement block,
            //thereby getting rid of result of the instanceof which
            //may stand before this mbs in the if-cascade
            popLevel();

            //get actual and formal parameter terms
            final ArrayOfParameterDeclaration parDecls = pm.getParameters();
            final int numPars = parDecls.size();
            final TypeSchemeTerm actualParTerms[] = new TypeSchemeTerm[numPars];
            final TypeSchemeTerm formalParTerms[] = new TypeSchemeTerm[numPars];
            for(int i = numPars - 1; i >= 0; i--) {
                actualParTerms[i] = pop();
                    
                ParameterDeclaration parDecl
                            = parDecls.getParameterDeclaration(i);
                VariableSpecification parSpec
                            = parDecl.getVariableSpecification();
                ProgramVariable formalParVar
                            = (ProgramVariable) parSpec.getProgramVariable();
                formalParTerms[i]
                            = (pm.isStatic()
                               ? checker.checkStaticLocalVariable(formalParVar)
                               : checker.checkInstanceLocalVariable(formalParVar));                    
            }

            //get receiver term
            final TypeSchemeTerm receiverTerm = pop();

            //get formal result term
	    final ProgramVariable formalResultVar 
                  = (ProgramVariable) x.getResultVariable();
            final TypeSchemeTerm formalResultTerm
                  = (formalResultVar == null
		     ? null
  		     : (pm.isStatic()
                        ? checker.checkStaticLocalVariable(formalResultVar)
                        : checker.checkInstanceLocalVariable(formalResultVar)));

            //generate constraints
            final TypeSchemeTerm actualResultTerm;
            if(isAllocation) {
                actualResultTerm
                        = checker.checkAllocation(actualParTerms,
                                                  formalParTerms);
            } else if(isStatic) {
                actualResultTerm
                        = checker.checkStaticMethodCall(actualParTerms,
                                                        formalParTerms,
                                                        formalResultTerm);
            } else {
                actualResultTerm
                        = checker.checkInstanceMethodCall(receiverTerm,
                                                          actualParTerms,
                                                          formalParTerms,
                                                          formalResultTerm);
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
                                = new ExecutionContext(classContext, null,
                                                       runtimeInstance);
                                                       
                //save context information
                final SVInstantiations oldSvInst 
                                = svInst;
                final TypeSchemeTerm oldContextFormalResultTerm 
                                = contextFormalResultTerm;
                                                       
                //adapt context information
                svInst                     = svInst.replace(null, 
                                                            null,
                                                            executionContext, 
                                                            body);
                contextFormalResultTerm    = formalResultTerm;
                
                //walk the body
                verbose("=========body enter (" + pm + ")=========");
                pushLevel();
                walk(body);
                popLevel();
                verbose("=========body exit (" + pm + ")==========");
                
                //restore context information
                svInst                     = oldSvInst;
                contextFormalResultTerm    = oldContextFormalResultTerm;
            }

            //push result term
            if(actualResultTerm != null) {
                push(actualResultTerm);
            }

            //re-push receiver and actual parameter terms, so that other
            //members of the the if-cascade can get them as well
            push(receiverTerm);
            for(int i = 0; i < numPars; i++) {
                push(actualParTerms[i]);
            }

            //re-push the enclosing statement block's level mark
            pushLevel();
        }
    }

    
    public void performActionOnCatchAllStatement(CatchAllStatement x) {
        failUnexpected(x);
    }

     
    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
        //nothing to do
    }

    
    public void performActionOnImport(Import x) {
        failUnexpected(x);
    }

    
    public void performActionOnExtends(Extends x) {
        failUnexpected(x);
    }

    
    public void performActionOnImplements(Implements x) {
        failUnexpected(x);
    }

    
    public void performActionOnVariableSpecification(VariableSpecification x) {
        if(!entering) {
            //skip assignments with "invisible" variables
            //Rationale: A method reference, say "e1.m(e2)" is simplified to
            //"v1.m(v2)", where v1 and v2 are "invisible" variables, and
            //then passed to The MethodCall metaconstruct, which replaces it
            //by "p#1 = v2; v1.m(p#1);". However, since
            //performActionOnMethodBodyStatement() actually works directly on
            //the real receiver e1 and the real parameter e2, none of these
            //intermediate helper variables occurs in the constraints which are
            //generated for the method call. Thus, creating constraints for the
            //assignments between them would be superfluous.
            if(x.getInitializer() instanceof ProgramVariable
               && ((ProgramVariable) x.getInitializer())
                  .getProgramElementName() == INVISIBLE_NAME) {
                return;
            }
        
            if(x.getInitializer() instanceof ArrayInitializer) {
                ArrayInitializer ai = (ArrayInitializer) x.getInitializer();
                
                TypeSchemeTerm[] initTerms
                                = new TypeSchemeTerm[ai.getExpressionCount()];
                for(int i = ai.getExpressionCount() - 1; i >= 0; i--) {
                    initTerms[i] = pop();
                }
                TypeSchemeTerm arrayTerm = pop();
                
                Expression arrayExpr = (Expression) x.getChildAt(0);
                Sort arraySort
                    = arrayExpr.getKeYJavaType(services,
                                               svInst.getExecutionContext())
                               .getSort();

                TypeSchemeTerm referenceTerm
                                = checker.checkArrayAccess(arraySort,
                                                           arrayTerm,
                                                           null);

                for(int i = 0; i < ai.getExpressionCount(); i++) {
                    checker.checkAssignment(referenceTerm, initTerms[i]);
                }
                
                push(arrayTerm);
            } else {
                TypeSchemeTerm initTerm = (x.hasInitializer() ? pop() : null);
                TypeSchemeTerm varTerm = pop();
        
                if(initTerm != null) {
                    checker.checkAssignment(varTerm, initTerm);
                }
                
                push(varTerm);
            }
        }
    }

     
    public void performActionOnFieldSpecification(FieldSpecification x) {
        failUnexpected(x);
    }

    
    public void performActionOnImplicitFieldSpecification(
                                                ImplicitFieldSpecification x) {
        failUnexpected(x);
    }
    
    
    public void performActionOnBinaryAnd(BinaryAnd x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnCopyAssignment(CopyAssignment x) {
        if(!entering) {
            TypeSchemeTerm rhsTerm = pop();
            TypeSchemeTerm lhsTerm = pop();
               
            TypeSchemeTerm assignmentTerm
                        = checker.checkAssignment(lhsTerm, rhsTerm);
        
            push(assignmentTerm);
        }
    }

    
    public void performActionOnDivideAssignment(DivideAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnMinusAssignment(MinusAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnModuloAssignment(ModuloAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnPlusAssignment(PlusAssignment x) {
        performActionOnPrimitiveBinary();
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

    
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
        performActionOnPrimitiveBinary();
    }
    

    public void performActionOnTimesAssignment(TimesAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnUnsignedShiftRightAssignment(
                                            UnsignedShiftRightAssignment x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryNot(BinaryNot x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryOr(BinaryOr x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnBinaryXOr(BinaryXOr x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnConditional(Conditional x) {
        if(!entering) {
            TypeSchemeTerm elseTerm = pop();
            TypeSchemeTerm thenTerm = pop();
            TypeSchemeTerm conditionTerm = pop();
            
            TypeSchemeTerm conditionalTerm
                        = checker.checkConditional(conditionTerm,
                                                   thenTerm,
                                                   elseTerm);

            push(conditionalTerm);
        }
    }
        
    
    public void performActionOnDivide(Divide x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnEquals(Equals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnGreaterThan(GreaterThan x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnLessOrEquals(LessOrEquals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnLessThan(LessThan x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnNotEquals(NotEquals x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnNewArray(NewArray x) {
        if(!entering) {
	    ArrayInitializer ai = x.getArrayInitializer();
	    TypeSchemeTerm sizeTerm = (ai == null ? pop() : null);

	    TypeSchemeTerm arrayTerm
                        = checker.checkArrayAllocation(sizeTerm);

	    if(ai != null) {
                Sort arraySort = x.getKeYJavaType().getSort();
		TypeSchemeTerm referenceTerm
				= checker.checkArrayAccess(arraySort,
                                                           arrayTerm,
                                                           null);
		for(int i = 0; i < ai.getExpressionCount(); i++) {
		    TypeSchemeTerm initTerm = pop();
		    checker.checkAssignment(referenceTerm, initTerm);
		}
	    }
		
	    push(arrayTerm);
	}
    }

    
    public void performActionOnInstanceof(Instanceof x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnExactInstanceof(ExactInstanceof x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnNew(New x) {
        if(entering) {
            //get the new-object type
            KeYJavaType newObjectType
                              = x.getKeYJavaType(services, 
                                                 svInst.getExecutionContext());
            assert newObjectType != null;

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
            final ArrayOfExpression args = x.getArguments();
            adoptedChildren = new ProgramElement[args.size() + 2];
            adoptedChildren[0] = new ThisReference();
            for(int i = 0; i < args.size(); i++) {
                adoptedChildren[i + 1] = args.getExpression(i);
            }
            adoptedChildren[args.size() + 1] = expandedPe;

            pushLevel();
        } else {
            //get rid of superfluous terms on the stack, but leave the topmost
            //non-LEVEL element as result
            ListOfTypeSchemeTerm resultTerms = popLevel();
            if(resultTerms.size() > 0) {
                push(resultTerms.head());
            }
	}
    }

    
    public void performActionOnTypeCast(TypeCast x) {
        //nothing to do
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

    
    public void performActionOnMinus(Minus x) {
        performActionOnPrimitiveBinary();
    }

     
    public void performActionOnModulo(Modulo x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnNegative(Negative x) {
        performActionOnPrimitiveUnary();
    }

    
    public void performActionOnPlus(Plus x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnPositive(Positive x) {
        performActionOnPrimitiveUnary();
    }

     
    public void performActionOnShiftLeft(ShiftLeft x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnShiftRight(ShiftRight x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnTimes(Times x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x) {
        performActionOnPrimitiveBinary();
    }

    
    public void performActionOnArrayReference(ArrayReference x) {
        if(!entering) {
	    TypeSchemeTerm positionTerm = pop();
            TypeSchemeTerm receiverTerm = pop();
            
            Expression arrayExpr = (Expression) x.getChildAt(0);
            Sort arraySort
                    = arrayExpr.getKeYJavaType(services,
                                               svInst.getExecutionContext())
                               .getSort();

	    TypeSchemeTerm referenceTerm
                    = checker.checkArrayAccess(arraySort,
                                               receiverTerm,
                                               positionTerm);

	    push(referenceTerm);
        }
    }

     
    public void performActionOnMetaClassReference(MetaClassReference x) {
        failUnexpected(x);
    }
    
             
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
	    final ArrayOfExpression args = x.getArguments();
            adoptedChildren = new ProgramElement[args.size() + 2];
	    adoptedChildren[0] = (rp instanceof Expression
                                  ? rp
                                  : new ThisReference());
	    for(int i = 0; i < args.size(); i++) {
		adoptedChildren[i + 1] = args.getExpression(i);
	    }
	    adoptedChildren[args.size() + 1] = expandedPe;

            pushLevel();
        } else {
            //get rid of superfluous terms on the stack, but leave the topmost
            //non-LEVEL element as potential result
            ListOfTypeSchemeTerm resultTerms = popLevel();
            if(resultTerms.size() > 0) {
                push(resultTerms.head());
            }
        }
    }

    
    public void performActionOnFieldReference(FieldReference x) {
        if(!entering) {
            TypeSchemeTerm referenceTerm;
                      
            TypeSchemeTerm fieldTerm = pop();
    
            if(x.getProgramVariable().isStatic()) {
                referenceTerm = checker.checkStaticFieldAccess(fieldTerm);
            } else {
                TypeSchemeTerm receiverTerm
                                = (x.getReferencePrefix() == null
                                   ? checker.checkThis()
                                   : pop());
                referenceTerm = checker.checkInstanceFieldAccess(receiverTerm,
                                                                 fieldTerm);
            }
                
            push(referenceTerm);
        }
    }

    
    public void performActionOnSchematicFieldReference(
                                                    SchematicFieldReference x) {
        failUnexpected(x);
    }

    
    public void performActionOnVariableReference(VariableReference x) {
        //nothing to do
    }

    
    public void performActionOnMethod(ProgramMethod x) {
        failUnexpected(x);
    }

    
    public void performActionOnSuperConstructorReference(
                                                SuperConstructorReference x) {
        //never met, because ConstructorCall replaces it with
        //ordinary MethodReference
        failUnexpected(x); 
    }

    
    public void performActionOnExecutionContext(ExecutionContext x) {
        failUnexpected(x);
    }

    
    public void performActionOnConstructorDeclaration(
                                                ConstructorDeclaration x) {
        failUnexpected(x);
    }

    
    public void performActionOnThisConstructorReference(
                                                ThisConstructorReference x) {
        //never met, because ConstructorCall replaces it with
        //ordinary MethodReference
        failUnexpected(x);
    }

    
    public void performActionOnSuperReference(SuperReference x) {
        if(!entering) {
            TypeSchemeTerm superTerm = checker.checkSuper();
            push(superTerm);
        }
    }

    
    public void performActionOnThisReference(ThisReference x) {
        if(!entering) {
            TypeSchemeTerm thisTerm = checker.checkThis();
            push(thisTerm);
        }
    }

    
    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
        performActionOnPrimitiveLiteral();
    }
    

    public void performActionOnThen(Then x) {
        //nothing to do
    }

    
    public void performActionOnElse(Else x) {
        //nothing to do
    }

    
    public void performActionOnCase(Case x) {
        //nothing to do
    }

    
    public void performActionOnCatch(Catch x) {
        if(!entering) {
            TypeSchemeTerm excTerm = pop();
            checker.checkCatch(excTerm);
        }
    }

     
    public void performActionOnDefault(Default x) {
        //nothing to do
    }

    
    public void performActionOnFinally(Finally x) {
        //nothing to do
    }

    
    public void performActionOnModifier(Modifier x) {
        failUnexpected(x);
    }

    
    public void performActionOnEmptyStatement(EmptyStatement x) {
        //nothing to do
    }

    
    public void performActionOnComment(Comment x) {
        //nothing to do
    }

    
    public void performActionOnParenthesizedExpression(
                                                    ParenthesizedExpression x) {
        //nothing to do
    }

    
    public void performActionOnPassiveExpression(PassiveExpression x) {
        //nothing to do
    }

    
    public void performActionOnForUpdates(ForUpdates x) {
        //nothing to do
    }

    
    public void performActionOnGuard(Guard x) {
        //nothing to do
    }

    
    public void performActionOnLoopInit(LoopInit x) {
        //nothing to do
    }
  
    public void performActionOnAssert(Assert assert1) {        
        //nothing to do        
    }
    
    public void performActionOnProgramSVSkolem(ProgramSVSkolem x) {
        failUnexpected(x);
    }
    

    public void performActionOnProgramSVProxy(ProgramSVProxy x) {
        failUnexpected(x);
    }


    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }


    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);        
    }


  
}
