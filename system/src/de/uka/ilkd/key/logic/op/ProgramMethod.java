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

package de.uka.ilkd.key.logic.op;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.Throws;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * The program method represents a (pure) method in the logic.
 * In case of a non-static method the first argument represents the 
 * object on which the method is invoked. 
 */
public final class ProgramMethod extends ObserverFunction 
    			  	 implements ProgramInLogic, IProgramMethod {

    private final MethodDeclaration method;
    /** Return type of the method. Must not be null. Use KeYJavaType.VOID_TYPE for void methods. */
    private final KeYJavaType returnType;
    private final PositionInfo pi;
    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     
    public ProgramMethod(MethodDeclaration method,
        KeYJavaType container,
    	KeYJavaType kjt,
    	PositionInfo pi,
    	final Sort heapSort) {
    	this(method, container, kjt, pi, heapSort, 1);
    }
  
    public ProgramMethod(MethodDeclaration method, 
			 KeYJavaType container, 
			 KeYJavaType kjt,
                         PositionInfo pi,
                         Sort heapSort,
                         int heapCount) {
        super(method.getProgramElementName().toString(), 
              kjt.getSort(),
              kjt,
              heapSort,
              container,
              method.isStatic(),
              getParamTypes(method),
              heapCount,
              method.getStateCount());
        this.method  = method;
        this.returnType     = kjt;
        this.pi      = pi;
    }
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------     


    private static ImmutableArray<KeYJavaType> getParamTypes(
	    					MethodDeclaration md) {
	KeYJavaType[] result 
		= new KeYJavaType[md.getParameterDeclarationCount()];
	for(int i = 0; i < result.length; i++) {
	    result[i] = md.getParameterDeclarationAt(i)
	    		  .getVariableSpecification()
	    		  .getProgramVariable()
	                  .getKeYJavaType();
	}
	return new ImmutableArray<KeYJavaType>(result);
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------     

    // convenience methods to access methods of the corresponding MethodDeclaration
    // in a direct way
   
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getMethodDeclaration()
    */
   @Override
   public MethodDeclaration getMethodDeclaration() {
	return method;
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getParameterType(int)
    */
    @Override
   public KeYJavaType getParameterType(int i) {
       return method.getParameterDeclarationAt(i).getVariableSpecification().getProgramVariable().getKeYJavaType(); 
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getBody()
    */
   @Override
   public StatementBlock getBody() {
        return getMethodDeclaration().getBody();
    }

    @Override
    public SourceElement getFirstElement(){
	return this;
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
       return getFirstElement();
    }

    @Override
    public SourceElement getLastElement(){
	return this;
    }

    @Override
    public Comment[] getComments() {
	return method.getComments();
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
	method.prettyPrint(w);
    }

    /** 
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
	v.performActionOnProgramMethod(this);
    }

    /**
     *        Returns the start position of the primary token of this element.
     *        To get the start position of the syntactical first token,
     *        call the corresponding method of <CODE>getFirstElement()</CODE>.
     *        @return the start position of the primary token.
    */
    @Override    
    public Position getStartPosition(){
	return pi.getStartPosition();
    }

    /**
     *        Returns the end position of the primary token of this element.
     *        To get the end position of the syntactical first token,
     *        call the corresponding method of <CODE>getLastElement()</CODE>.
     *        @return the end position of the primary token.
     */
    @Override
    public Position getEndPosition(){
	return pi.getEndPosition();
    }

    /**
     *        Returns the relative position (number of blank heading lines and 
     *        columns) of the primary token of this element.
     *        To get the relative position of the syntactical first token,
     *        call the corresponding method of <CODE>getFirstElement()</CODE>.
     *        @return the relative position of the primary token.
     */
    @Override
    public Position getRelativePosition(){
	return  pi.getRelativePosition();
    }


    @Override
    public PositionInfo getPositionInfo(){
	return  pi;
    }


    /**
     * Test whether the declaration is private.
     */
    @Override
    public boolean isPrivate(){
	return method.isPrivate();
    }

    /**
     * Test whether the declaration is protected.
     */
    @Override
    public boolean isProtected(){
	return method.isProtected();
    }

    /**
     * Test whether the declaration is public.
     */
    @Override
    public boolean isPublic(){
	return method.isPublic();
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isConstructor()
    */
    @Override
   public boolean isConstructor(){
	return method instanceof Constructor;
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isModel()
    */
    @Override
   public boolean isModel() {
        return method.isModel();
    }

    /**
     * Test whether the declaration is strictfp.
     */
    @Override
    public boolean isStrictFp(){
	return method.isStrictFp();
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isVoid()
    */
   @Override
   public boolean isVoid(){
        return returnType == KeYJavaType.VOID_TYPE && !isConstructor();
    }
    
    @Override
    public ImmutableArray<Modifier> getModifiers(){
	return method.getModifiers();
    }

    @Override
    public int getChildCount() {
	return 0;
    }

    @Override
    public ProgramElement getChildAt(int i){
       return null;
    }
  
    /** equals modulo renaming is described in class
     * SourceElement.
     */
    @Override
    public boolean equalsModRenaming(SourceElement se, 
	    NameAbstractionTable nat) {
	if (se == null || !(se instanceof IProgramMethod)) {
	    return false;
	}

	return method==((IProgramMethod)se).getMethodDeclaration();
    }
    
    @Deprecated
    public KeYJavaType getKJT(){
        return returnType;
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getReturnType()
    */
    @Override
   public KeYJavaType getReturnType() {
        return returnType;
    }

    @Override
    public Expression convertToProgram(Term t, ExtList l) {
	ProgramElement called;
	if (isStatic()) {
	    called = new TypeRef(getContainerType());
	} else {
	    called=(ProgramElement)l.get(0);
	    l.remove(0);
	}
	return new MethodReference(l, getProgramElementName(), 
				   (ReferencePrefix) called);
    }   
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getProgramElementName()
    */
   @Override
   public ProgramElementName getProgramElementName() {
	return getMethodDeclaration().getProgramElementName();
    }

   /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getUniqueName()
    */
   @Override
   public String getUniqueName() {
       return getName() + "_" +
              Math.abs(ContractFactory.generateContractTypeName("",
                                                                getContainerType(),
                                                                this,
                                                                getContainerType()
                                                                ).hashCode());
    } // Included HashCode to make IF-Predicates unique and still reproducible

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getFullName()
    */
   @Override
   public String getFullName() {
       return getMethodDeclaration().getFullName();
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getName()
    */
   @Override
   public String getName() {
    	return getMethodDeclaration().getName();
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isAbstract()
    */
   @Override
   public boolean isAbstract() {
    	return getMethodDeclaration().isAbstract();
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isImplicit()
    */
   @Override
   public boolean isImplicit(){
	return getName().startsWith("<");
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isNative()
    */
   @Override
   public boolean isNative() {
    	return getMethodDeclaration().isNative();
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isFinal()
    */
   @Override
   public boolean isFinal() {
    	return getMethodDeclaration().isFinal();
    }

    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#isSynchronized()
    */
   @Override
   public boolean isSynchronized() {
    	return getMethodDeclaration().isSynchronized();
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getThrown()
    */
   @Override
   public Throws getThrown() {
        return getMethodDeclaration().getThrown();
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getParameterDeclarationAt(int)
    */
   @Override
   public ParameterDeclaration getParameterDeclarationAt(int index) {
    	return getMethodDeclaration().getParameterDeclarationAt(index);
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getVariableSpecification(int)
    */
    @Override
   public VariableSpecification getVariableSpecification(int index) {
        return method.getParameterDeclarationAt(index).getVariableSpecification();
    }
     
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getParameterDeclarationCount()
    */
   @Override
   public int getParameterDeclarationCount() {
    	return getMethodDeclaration().getParameterDeclarationCount();
    }
    
    /* (non-Javadoc)
    * @see de.uka.ilkd.key.logic.op.IProgramMethod#getParameters()
    */
   @Override
   public ImmutableArray<ParameterDeclaration> getParameters() {
    	return getMethodDeclaration().getParameters();
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (src == this) {
            source.next();
            return matchCond;
        } else {
            Debug.out("Program match failed (pattern, source)", this, src);
            return null;
        }        
    }
}
