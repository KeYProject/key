// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** This file represents a Java method in the logic. It is part of the
 * AST of a java program 
 */
package de.uka.ilkd.key.logic.op;

import java.io.IOException;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.annotation.Annotation;
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
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * The program method represents a concrete method in the logic.
 * In case of an instance method the first argument represents the 
 * object on which the method is invoked. 
 */
public class ProgramMethod extends NonRigidFunction 
    implements SourceElement, ProgramElement, 
    MemberDeclaration, ProgramInLogic, Contractable {

    private final MethodDeclaration method; 
    private final KeYJavaType kjt;
    private final KeYJavaType contKJT;
    private final PositionInfo pi;
    
    
    public ProgramMethod(MethodDeclaration method, 
			 KeYJavaType contKJT, 
			 KeYJavaType kjt,
                         PositionInfo pi) {
	// for some reasons pm are created for void methods too. It's odd,
        // but expand method body relies on a pm....
        super(new ProgramElementName(method.getProgramElementName().toString(), 
                contKJT.getSort().toString()), 
	      kjt == null ? null : kjt.getSort(), getArgumentSorts(method, contKJT));
                        
	this.method  = method;
	this.contKJT = contKJT;
	this.kjt     = kjt;
        this.pi      = pi;
        
    }
    

   /**
    * determines the argument sorts of the symbol to be created 
    * @param md the MethodDeclaration whose signature is used as blueprint
    * @param container the KeYJavaType of the type where this method is declared
    * @return the symbols argument sorts
    */
   private static Sort[] getArgumentSorts(MethodDeclaration md, KeYJavaType container) {  
       final boolean instanceMethod = !md.isStatic() && !(md instanceof Constructor);
       
       final int arity = instanceMethod ? 
               md.getParameterDeclarationCount() + 1 : md.getParameterDeclarationCount();       
       
       final Sort[] argSorts = new Sort[arity];
 
       final int offset;
       
       if (instanceMethod) {  
           argSorts[0] = container.getSort();           
           offset = 1;
       } else {
           offset = 0;
       }
       
       for (int i = offset; i<argSorts.length; i++) {
           argSorts[i] = 
               md.getParameterDeclarationAt(i-offset).
               getTypeReference().getKeYJavaType().getSort();
       }
       return argSorts;
    }
   
   /**
    * BUG: remove this method bit first adopt the jml translation to take about the 
    * correct type of parameters and automatic type conversion    
    * @return true iff number of subterms of term is equal 
    * to its own arity
    *    
    */   
   public boolean validTopLevel(Term term){   
       return term.arity()==this.arity(); //%%% needs more checking!!!!   
   }   


    // convienience methods to access methods of the corresponding MethodDeclaration
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
       return method.getParameterDeclarationAt(i).getTypeReference().getKeYJavaType(); 
    }
    
    public StatementBlock getBody() {
        return getMethodDeclaration().getBody();
    }

    /** toString */
    public String toString() {
	return name().toString();
    }

    public SourceElement getFirstElement(){
	return method.getFirstElement();
    }

    public SourceElement getLastElement(){
	return method.getLastElement();
    }

    public Comment[] getComments() {
	return method.getComments();
    }

    /**
     *@return the annotations.
     */
    public Annotation[] getAnnotations(){
	return new Annotation[0];
    }

    public int getAnnotationCount(){
	return 0;
    }

    public void prettyPrint(PrettyPrinter w) throws IOException {
	method.prettyPrint(w);
    }

    /** 
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnProgramMethod(this);
    }

    /**
 *        Returns the start position of the primary token of this element.
 *        To get the start position of the syntactical first token,
 *        call the corresponding method of <CODE>getFirstElement()</CODE>.
 *        @return the start position of the primary token.
    */
    public Position getStartPosition(){
	return pi.getStartPosition();
    }

    /**
 *        Returns the end position of the primary token of this element.
 *        To get the end position of the syntactical first token,
 *        call the corresponding method of <CODE>getLastElement()</CODE>.
 *        @return the end position of the primary token.
     */
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
    public Position getRelativePosition(){
	return  pi.getRelativePosition();
    }


    public PositionInfo getPositionInfo(){
	return  pi;
    }


    /**
     * Test whether the declaration is private.
     */
    public boolean isPrivate(){
	return method.isPrivate();
    }

    /**
     * Test whether the declaration is protected.
     */
    public boolean isProtected(){
	return method.isProtected();
    }

    /**
     * Test whether the declaration is public.
     */
    public boolean isPublic(){
	return method.isPublic();
    }

    /**
     * Test whether the declaration is static.
     */
    public boolean isStatic(){
	return method.isStatic();
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
    public boolean isStrictFp(){
	return method.isStrictFp();
    }
    
    public ArrayOfModifier getModifiers(){
	return method.getModifiers();
    }

    public int getChildCount() {
	return method.getChildCount();
    }

    public ProgramElement getChildAt(int i){
	return method.getChildAt(i);
    }
  
    /** equals modulo renaming is described in class
     * SourceElement.
     */
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

    public KeYJavaType getContainerType() {
	return contKJT;
    }

    public Expression convertToProgram(Term t, ExtList l) {
	ProgramElement called;
	if (isStatic()) {
	    called = new TypeRef(contKJT);
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

    public boolean equalContractable(Contractable c) {
    	return equals(c) 
	  && getContainerType().equals
	       (((ProgramMethod)c).getContainerType());
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
    
    /** returns the variablespecification of the i-th parameterdeclaration */
    public VariableSpecification getVariableSpecification(int index) {
        return method.getParameterDeclarationAt(index).getVariableSpecification();
    }
     
    public int getParameterDeclarationCount() {
    	return getMethodDeclaration().getParameterDeclarationCount();
    }
    
    public ArrayOfParameterDeclaration getParameters() {
    	return getMethodDeclaration().getParameters();
    }

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
