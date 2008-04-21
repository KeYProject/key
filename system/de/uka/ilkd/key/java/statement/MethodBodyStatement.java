// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.ExtList;


/**
 *  A shortcut-statement for a method body, i.e. no dynamic dispatching 
 *  any longer.<p /> 
 *  Please take care:
 *  only the method name plus the class in which class the method 
 *  is implemented is part of the syntax representation of such a 
 *  statement, but not the methods complete syntax. If there are 
 *  two methods with an equal name, but different signature (i.e.
 *  parameter types), the pure syntax is ambigious. In fact the concrete body 
 *  this method body statement represents depends on the static type of 
 *  its arguments. <p />
 *  Therefore: Transformation of a method body statement <em>MUST</em> keep
 *  the static type of the arguments <em>unchanged</em>.
 *  <p />
 *     
 *       
 */
public class MethodBodyStatement extends JavaNonTerminalProgramElement
    implements Statement, NonTerminalProgramElement {

    
    /** 
     * the variable the result of the method execution is assigned to
     * if the method is declared void or the result not assigned to a 
     * variable or field, this value is null.
     */
    private final IProgramVariable resultVar;
            
    /**
     * This type reference determines the class where the represented method
     * has to be implemented.
     */
    private final TypeReference bodySource;

    /** 
     * the reference describing the method signature
     */
    private final MethodReference methodReference;
    
    /** cache resolved method */
    private ProgramMethod method;

    /** indicates whether this stands for the specification of 
     * a method rather than the concrete body*/
    private boolean useSpecification;
    
    /**
     *      Construct a method body shortcut
     *      @param bodySource exact class where the body is declared
     *      @param resultVar the IProgramVariable to which the method's return value is assigned
     *      @param methodReference the MethodReference encapsulating the method's signature  
     */
     public MethodBodyStatement(TypeReference bodySource,
                                IProgramVariable resultVar,                                
                                MethodReference methodReference) {
         this.bodySource      = bodySource;	 
	 this.resultVar       = resultVar;
	 this.methodReference = methodReference;
	 
         assert methodReference != null : "Missing methodreference";
         assert methodReference.getReferencePrefix() != null : 
             "Method reference of a method body statement needs an " +
             "explicit reference prefix.";
     }
    
    public MethodBodyStatement(ExtList list) {        
        this.bodySource = (TypeReference) list.get(TypeReference.class);
        this.resultVar  = (IProgramVariable) list.get(IProgramVariable.class);
        
        this.methodReference = (MethodReference)list.get(MethodReference.class);
        
        assert methodReference != null : "Missing methodreference";
        assert methodReference.getReferencePrefix() != null : 
            "Method reference of a method body statement needs an " +
            "explicit reference prefix.";
    }    



    public MethodBodyStatement(ProgramMethod method, 
                               ReferencePrefix newContext, 
                               IProgramVariable res, 
                               ArrayOfExpression args,
                               boolean useSpecification) {
        this.method = method;
        this.bodySource = 
            new TypeRef(method.getContainerType());
        this.resultVar = res;
        this.useSpecification = useSpecification;
        
        if (newContext == null) {
            if (method.isStatic()) {
                newContext = bodySource; 
            } else {
                throw new IllegalArgumentException("The invocation target of a method body" +
                                "statement must be non null");
            }
        }
        
        this.methodReference = new MethodReference(args, 
                                                   method.getProgramElementName(), 
                                                   newContext);
    }



    public MethodBodyStatement(ProgramMethod method, 
            ReferencePrefix newContext, 
            IProgramVariable res, 
            ArrayOfExpression args) {
        this(method, newContext, res, args, false);
    }
    
    /**
     *      Get method body.
     *      @return the Statement
     */
    public Statement getBody(Services services) {
	if (method == null) {
	    resolveMethod(services);
        }
        return method.getBody();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
 	int i = 0;
	if (bodySource != null) i++;
        if (resultVar != null) i++;
        if (methodReference != null) i++;
	return i;
    }

    public ReferencePrefix getDesignatedContext() {
        return methodReference.getReferencePrefix();
    }
    
    public ArrayOfExpression getArguments() {
        return methodReference.getArguments();
    }
    
    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array.
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */
    public ProgramElement getChildAt(int index) {
	if (bodySource != null) {
	    if (index == 0) {
	        return bodySource;
	    }
	    index--;
        }
        
        if (resultVar != null) {
            if (index == 0) {
                return resultVar;
            }
            index--;
        }
    
        if (methodReference != null) {
            if (index == 0) {
                return methodReference;
            }       
        }
                                               
 	throw new ArrayIndexOutOfBoundsException();
    }
        
    public boolean isStatic(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return method.isStatic();
    }

    /**
     * Tests for "@pure" annotation
     *
     * @see de.uka.ilkd.key.proof.mgt.SpecificationRepository#isStrictlyPure(ProgramMethod)
     * @param services
     * @return true, iff the method is annotated "@pure"
     */
    public boolean isPure(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return services.getSpecificationRepository().isStrictlyPure(method);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnMethodBodyStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
	p.printMethodBodyStatement(this);
    }
    
    public IProgramVariable getResultVariable() {
	return resultVar;
    }
    
    public KeYJavaType getBodySource() {         
        return bodySource.getKeYJavaType();
    }
    
    public TypeReference getBodySourceAsTypeReference() {         
        return bodySource;
    }
    
    
    public ProgramMethod getProgramMethod(Services services) {
        if (method == null) {
            resolveMethod(services);
        }
        return method;
    }

    private void resolveMethod(Services services) {
        method = services.getJavaInfo().
        getProgramMethod(getBodySource(), 
                         methodReference.getName(), 
                         services.getJavaInfo().
                         createSignature(methodReference.getArguments()),
                         getBodySource());        
    }

    public String reuseSignature(Services services, ExecutionContext ec) {
       return super.reuseSignature(services, ec)+"("+getBodySource().getName()+")";
    }

    
    
    public MethodReference getMethodReference() {
        return methodReference;
    }
    
    public boolean replaceBySpecification() {
        return useSpecification;
    }
    
}
