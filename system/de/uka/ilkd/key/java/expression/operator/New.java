// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.util.ExtList;

/**
 *  The object allocation operator.
 *  There are two variants for New:
 *  <OL>
 *  <LI>Class constructor call
 *  <BR><tt>new XYZ(a<sub>1</sub>, ..., a<sub>n</sub>)</tt>
 *  <BR>if getType() instanceof UserType
 *  <LI>Anonymous Inner Class definition and construction
 *  <BR><tt>new XYZ(a<sub>1</sub>, ..., a<sub>n</sub>)
 *  { m<sub>1</sub>, ..., m<sub>k</sub> }</tt>
 *  <BR>if getType() instanceof UserType && getClassDeclaration() != <tt>null</tt>
 *  </OL>
 *  The access path is <tt>null</tt> in most cases, except when an inner class
 *  constructor is invoked from an outer instance.
 */

public class New
 extends TypeOperator
 implements ConstructorReference, ExpressionStatement, ReferencePrefix, ReferenceSuffix, TypeDeclarationContainer {

    /**
     *      Anonymous class.
     */
    protected final ClassDeclaration anonymousClass;
    
    protected final ProgramElement scope;

    /**
     *      Access path.
     */
    protected final ReferencePrefix accessPath;

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *          a ClassDeclaration (in case of an anonymous class decl)
     *          a TypeReference (the referred type)
     * 		2 of Expression (the first Expression as left hand
     * 			side, the second as right hand side), 
     * 		Comments; 
     *              does NOT contain: a ReferencePrefix for the constructor
     * 		as it might be mixed up with the TypeReference
     * @param rp a ReferencePrefix as access path for the constructor     
     */
    public New(ExtList children, ReferencePrefix rp) {
	super(children);
	anonymousClass=(ClassDeclaration)children.get(ClassDeclaration.class);
        if(children.get(ProgramSV.class)!=null){
            scope = (ProgramSV) children.get(ProgramSV.class);
        }else{
            scope = (ProgramElementName) children.get(ProgramElementName.class);
        }
	accessPath=rp;
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *          a ClassDeclaration (in case of an anonymous class decl)
     *          a TypeReference (the referred type)
     * 		2 of Expression (the first Expression as left hand
     * 			side, the second as right hand side), 
     * 		Comments; 
     *              does NOT contain: a ReferencePrefix for the constructor
     * 		as it might be mixed up with the TypeReference
     * @param rp a ReferencePrefix as access path for the constructor     
     */
    public New(ExtList children, ReferencePrefix rp, PositionInfo pi) {
	super(children, pi);
	anonymousClass=(ClassDeclaration)children.get(ClassDeclaration.class);
        if(children.get(ProgramSV.class)!=null){
            scope = (ProgramSV) children.get(ProgramSV.class);
        }else{
            scope = (ProgramElementName) children.get(ProgramElementName.class);
        }
	accessPath=rp;
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param type a TypeReference (the referred type)
     * @param rp a ReferencePrefix as access path for the constructor     
     */
    public New(Expression[] arguments, TypeReference type, ReferencePrefix rp, ProgramElementName scope) {
	super(arguments, type);
	anonymousClass = null;
	accessPath = rp;
        if(scope==null){
            this.scope = new ProgramElementName(MethodReference.LOCAL_SCOPE);
        }else{
            this.scope = scope;
        }
    }
    
    public New(Expression[] arguments, TypeReference type, ReferencePrefix rp) {
        this(arguments, type, rp, null);
    }

    public SourceElement getFirstElement() {
        return (accessPath != null) ? accessPath.getFirstElement() : this;
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }


    /**
     *      Get arity.
     *      @return the int value.
     */
    public int getArity() {
        return 0;
    }

    /**
     *      Get precedence.
     *      @return the int value.
     */
    public int getPrecedence() {
        return 0;
    }

    /**
     *      Get notation.
     *      @return the int value.
     */
    public int getNotation() {
        return PREFIX;
    }

    /**
     *      Get class declaration.
     *      @return the class declaration.
     */
    public ClassDeclaration getClassDeclaration() {
        return anonymousClass;
    }

    /**
     *      Get the number of type declarations in this container.
     *      @return the number of type declarations.
     */
    public int getTypeDeclarationCount() {
        return (anonymousClass != null) ? 1 : 0;
    }

    /*
      Return the type declaration at the specified index in this node's
      "virtual" type declaration array.
      @param index an index for a type declaration.
      @return the type declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (anonymousClass != null && index == 0) {
            return anonymousClass;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (accessPath     != null) result++;
        if (typeReference  != null) result++;
        if (children       != null) result += children.size();
        if (scope != null) result++;
        if (anonymousClass != null) result++;
        return result;
    }

    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */
    public ProgramElement getChildAt(int index) {
        int len;
        if (accessPath != null) {
            if (index == 0) return accessPath;
            index--;
        }
        if (typeReference != null) {
            if (index == 0) return typeReference;
            index--;
        }
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.getExpression(index);
            }
            index -= len;
        }
        if (scope != null) {
            if (index == 0) return scope;
            index--;
        }
        if (anonymousClass != null) {
            if (index == 0) return anonymousClass;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get reference prefix.
     *      @return the reference prefix.
     */
    public ReferencePrefix getReferencePrefix() {
        return accessPath;
    }
    
    public ProgramElement getScope(){
        return scope;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnNew(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printNew(this);
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }
}
