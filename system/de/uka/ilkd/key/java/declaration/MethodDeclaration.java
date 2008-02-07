// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.declaration;

import java.util.LinkedList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Method;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Method declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public class MethodDeclaration
 extends JavaDeclaration
 implements MemberDeclaration,
           TypeReferenceContainer,
           NamedProgramElement,
           ParameterContainer,
           Method,
           VariableScope{

    /**
 *      Return type.
     */

    protected final TypeReference returnType;

    /**
 *      Name.
     */

    protected final ProgramElementName name;

    /**
 *      Parameters.
     */

    protected final ArrayOfParameterDeclaration parameters;

    /**
 *      Exceptions.
     */

    protected final Throws exceptions;

    /**
 *      Body.
     */

    protected final StatementBlock body;


    /** this field stores if parent is an InterfaceDeclaration because we will be
     * unable to walk the tree upwards to check this
     */
    protected final boolean parentIsInterfaceDeclaration;


    /**
     *      Method declaration.
     * @param children an ExtList of children.  May
     * include: a TypeReference (as a reference to the return type), a
     * de.uka.ilkd.key.logic.ProgramElementName (as Name of the method),
     * several ParameterDeclaration (as parameters of the declared method), a
     * StatementBlock (as body of the declared method), several Modifier 
     * (taken as modifiers of the declaration), a Comment
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * parent is an InterfaceDeclaration 
     */
    public MethodDeclaration(ExtList children, 
			     boolean parentIsInterfaceDeclaration) {
	super(children);
	returnType=(TypeReference)children.get(TypeReference.class);
	name=(ProgramElementName)children.get(ProgramElementName.class);
	this.parameters=new
	    ArrayOfParameterDeclaration((ParameterDeclaration[])
				children.collect(ParameterDeclaration.class));  
	exceptions=(Throws)children.get(Throws.class);
	body=(StatementBlock)children.get(StatementBlock.class);
	this.parentIsInterfaceDeclaration=parentIsInterfaceDeclaration;
    }



    /**
     * Method declaration.
     * @param modifiers a modifier array
     * @param returnType a type reference.
     * @param name an identifier.
     * @param parameters a parameter declaration mutable list.
     * @param exceptions a throws.     
     * @param body a statement block.
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * parent is an InterfaceDeclaration 
     */

    public MethodDeclaration(Modifier[] modifiers, TypeReference returnType, 
			     ProgramElementName name,
			     ParameterDeclaration[] parameters, 
			     Throws exceptions, StatementBlock body, 
			     boolean parentIsInterfaceDeclaration) { 
	this(modifiers, returnType, name, 
	     new ArrayOfParameterDeclaration(parameters),
	     exceptions, body, parentIsInterfaceDeclaration);
    }

    /**
     * Method declaration.
     * @param modifiers a modifier array
     * @param returnType a type reference.
     * @param name an identifier.
     * @param parameters a parameter declaration mutable list.
     * @param exceptions a throws.     
     * @param body a statement block.
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * parent is an InterfaceDeclaration 
     */

    public MethodDeclaration(Modifier[] modifiers, TypeReference returnType, 
			     ProgramElementName name,
			     ArrayOfParameterDeclaration parameters, 
			     Throws exceptions, StatementBlock body, 
			     boolean parentIsInterfaceDeclaration) { 
	super(modifiers);
	this.returnType = returnType;
        this.name=name;
	this.parameters = parameters;  
        this.exceptions = exceptions;
	this.body = body;
	this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
    }

    public ProgramElementName getProgramElementName(){
	return name;
    }


     public SourceElement getFirstElement() {
        return getChildAt(0);
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }


    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (modArray   != null) result += modArray.size();
        if (returnType != null) result++;
        if (name       != null) result++;
        if (parameters != null) result += parameters.size();
        if (exceptions != null) result++;
        if (body       != null) result++;
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
        if (modArray != null) {
            len = modArray.size();
            if (len > index) {
                return modArray.getModifier(index);
            }
            index -= len;
        }
        if (returnType != null) {
            if (index == 0) return returnType;
            index--;
        }
        if (name != null) {
            if (index == 0) return name;
            index--;
        }
        if (parameters != null) {
            len = parameters.size();
            if (len > index) {
                return parameters.getParameterDeclaration(index);
            }
            index -= len;
        }
        if (exceptions != null) {
            if (index == 0) return exceptions;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get the number of statements in this container.
 *      @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for a statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (returnType != null) ? 1 : 0;
    }

    /*
      Return the type reference at the specified index in this node's
      "virtual" type reference array.
      @param index an index for a type reference.
      @return the type reference with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public TypeReference getTypeReferenceAt(int index) {
        if (returnType != null && index == 0) {
            return returnType;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get the number of parameters in this container.
 *      @return the number of parameters.
     */

    public int getParameterDeclarationCount() {
        return (parameters != null) ? parameters.size() : 0;
    }

    /*
      Return the parameter declaration at the specified index in this node's
      "virtual" parameter declaration array.
      @param index an index for a parameter declaration.
      @return the parameter declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (parameters != null) {
            return parameters.getParameterDeclaration(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get return type.
 *      @return the type reference.
     */

    public TypeReference getTypeReference() {
        return returnType;
    }


    public final String getName() {
        return (name == null) ? null : name.toString();
    }



    /**
 *      Get parameters.
 *      @return the parameter declaration array wrapper.
     */

    public ArrayOfParameterDeclaration getParameters() {
        return parameters;
    }

    public String getFullName() {
	return getName();
    }


    /**
 *      Get thrown.
 *      @return the throws.
     */

    public Throws getThrown() {
        return exceptions;
    }

    /**
 *      Get body.
 *      @return the statement block.
     */

    public StatementBlock getBody() {
        return body;
    }


    /**
     * Test whether the declaration is final.
     */

    public boolean isFinal() {
        return super.isFinal();
    }

    /**
     * Test whether the declaration is private.
     */

    public boolean isPrivate() {
        return super.isPrivate();
    }

    /**
     * Test whether the declaration is protected.
     */

    public boolean isProtected() {
        return super.isProtected();
    }

    /**
     * Test whether the declaration is public. Methods of interfaces
     * are always public.
     */

    public boolean isPublic() {
        return parentIsInterfaceDeclaration || super.isPublic();
    }

    /**
     * Test whether the declaration is static.
     */

    public boolean isStatic() {
        return super.isStatic();
    }

    /**
     * Test whether the declaration is model (the jml modifier is meant).
     */

    public boolean isModel() {
        return super.isModel();
    }

    /**
     * Test whether the declaration is strictfp.
     */

    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    /**
     * Test whether the declaration is abstract. Methods of interfaces
     * are always abstract.
     */

    public boolean isAbstract() {
        return  parentIsInterfaceDeclaration || super.isAbstract();
    }

    /**
     * Test whether the declaration is native. Constructors
     * are never native.
     */

    public boolean isNative() {
        return super.isNative();
    }


    /**
     * Test whether the declaration is synchronized.
     */

    public boolean isSynchronized() {
        return super.isSynchronized();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnMethodDeclaration(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMethodDeclaration(this);
    }
}
