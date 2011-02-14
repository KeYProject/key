// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * The program method represents a concrete method in the logic.
 * In case of an instance method the first argument represents the 
 * object on which the method is invoked. 
 */
public final class ProgramMethod extends ObserverFunction 
    			  	 implements SourceElement, ProgramElement, 
    			  	            MemberDeclaration, ProgramInLogic {

    private final MethodDeclaration method; 
    private final KeYJavaType kjt;
    private final PositionInfo pi;
    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     
    
    public ProgramMethod(MethodDeclaration method, 
			 KeYJavaType container, 
			 KeYJavaType kjt,
                         PositionInfo pi,
                         Sort heapSort) {
        super(method.getProgramElementName().toString(), 
              kjt == null ? Sort.ANY : kjt.getSort(),
              kjt,
              heapSort,
              container,
              method.isStatic(),
              getParamTypes(method)); 
                        
	this.method  = method;;
	this.kjt     = kjt;
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
	                  .getTypeReference()
	                  .getKeYJavaType();
	}
	return new ImmutableArray<KeYJavaType>(result);
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------     

    // convenience methods to access methods of the corresponding MethodDeclaration
    // in a direct way
   
    public MethodDeclaration getMethodDeclaration() {
	return method;
    }

    /**     
     * returns the KeYJavaType of the <tt>i</tt>-th paramter declaration. This method 
     * does not care about the invoker as argSort does.      
     * @param i the int specifying the parameter position
     * @return the KeYJavaType of the <tt>i</tt>-th parameter
     */
    public KeYJavaType getParameterType(int i) {
       return method.getParameterDeclarationAt(i).getVariableSpecification().getProgramVariable().getKeYJavaType(); 
    }
    
    public StatementBlock getBody() {
        return getMethodDeclaration().getBody();
    }

    @Override
    public SourceElement getFirstElement(){
	return method.getFirstElement();
    }

    @Override
    public SourceElement getLastElement(){
	return method.getLastElement();
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

    /**
     * Test whether the declaration is a constructor.
     */
    public boolean isConstructor(){
	return method instanceof Constructor;
    }

    /**
     * Test whether the declaration is model.
     */
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
    
    @Override
    public ImmutableArray<Modifier> getModifiers(){
	return method.getModifiers();
    }

    @Override
    public int getChildCount() {
	return method.getChildCount();
    }

    @Override
    public ProgramElement getChildAt(int i){
	return method.getChildAt(i);
    }
  
    /** equals modulo renaming is described in class
     * SourceElement.
     */
    @Override
    public boolean equalsModRenaming(SourceElement se, 
	    NameAbstractionTable nat) {
	if (se == null || !(se instanceof ProgramMethod)) {
	    return false;
	}

	return method==((ProgramMethod)se).getMethodDeclaration();
    }

    public KeYJavaType getKeYJavaType() {
	return kjt;
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
    
    public ProgramElementName getProgramElementName() {
	return getMethodDeclaration().getProgramElementName();
    }
    
    public String getFullName() {
    	return getMethodDeclaration().getFullName();
    }

    public String getName() {
    	return getMethodDeclaration().getName();
    }
    
    public boolean isAbstract() {
    	return getMethodDeclaration().isAbstract();
    }

    public boolean isImplicit(){
	return getName().startsWith("<");
    }
    
    public boolean isNative() {
    	return getMethodDeclaration().isNative();
    }

    public boolean isFinal() {
    	return getMethodDeclaration().isFinal();
    }

    public boolean isSynchronized() {
    	return getMethodDeclaration().isSynchronized();
    }
    
    public TypeReference getTypeReference() {
    	return getMethodDeclaration().getTypeReference();
    }
    
    public Throws getThrown() {
        return getMethodDeclaration().getThrown();
    }
    
    public ParameterDeclaration getParameterDeclarationAt(int index) {
    	return getMethodDeclaration().getParameterDeclarationAt(index);
    }
    
    /** 
     * Returns the variablespecification of the i-th parameterdeclaration 
     */
    public VariableSpecification getVariableSpecification(int index) {
        return method.getParameterDeclarationAt(index).getVariableSpecification();
    }
     
    public int getParameterDeclarationCount() {
    	return getMethodDeclaration().getParameterDeclarationCount();
    }
    
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
