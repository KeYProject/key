// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.collection.ImmutableArray;
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
public class MethodDeclaration extends JavaDeclaration
 			       implements MemberDeclaration,
 			                  TypeReferenceContainer,
 			                  NamedProgramElement,
 			                  ParameterContainer,
 			                  Method,
 			                  VariableScope {

    protected final TypeReference returnType;
    protected final Comment[] voidComments;
    protected final ProgramElementName name;
    protected final ImmutableArray<ParameterDeclaration> parameters;
    protected final Throws exceptions;
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
			     boolean parentIsInterfaceDeclaration,
			     Comment[] voidComments) {
	super(children);
	returnType = children.get(TypeReference.class);
	this.voidComments = voidComments;
	name = children.get(ProgramElementName.class);
	this.parameters = new
	    ImmutableArray<ParameterDeclaration>(children.collect(ParameterDeclaration.class));  
	exceptions = children.get(Throws.class);
	body = children.get(StatementBlock.class);
	this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
	assert returnType == null || voidComments == null;
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
    public MethodDeclaration(Modifier[] modifiers, 
	    		     TypeReference returnType, 
			     ProgramElementName name,
			     ParameterDeclaration[] parameters, 
			     Throws exceptions, 
			     StatementBlock body, 
			     boolean parentIsInterfaceDeclaration) { 
	this(modifiers, 
	     returnType, 
	     name, 
	     new ImmutableArray<ParameterDeclaration>(parameters),
	     exceptions, 
	     body, 
	     parentIsInterfaceDeclaration);
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
    public MethodDeclaration(Modifier[] modifiers, 
	    		     TypeReference returnType, 
			     ProgramElementName name,
			     ImmutableArray<ParameterDeclaration> parameters, 
			     Throws exceptions, 
			     StatementBlock body, 
			     boolean parentIsInterfaceDeclaration) { 
	super(modifiers);
	this.returnType = returnType;
	this.voidComments = null;
        this.name = name;
	this.parameters = parameters;  
        this.exceptions = exceptions;
	this.body = body;
	this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
    }

    
    @Override    
    public ProgramElementName getProgramElementName(){
	return name;
    }


    @Override    
    public SourceElement getFirstElement() {
        return getChildAt(0);
    }

    
    @Override    
    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }


    @Override
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

    
    @Override
    public ProgramElement getChildAt(int index) {
        int len;
        if (modArray != null) {
            len = modArray.size();
            if (len > index) {
                return modArray.get(index);
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
                return parameters.get(index);
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


    @Override
    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    
    @Override
    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    @Override
    public int getTypeReferenceCount() {
        return (returnType != null) ? 1 : 0;
    }

    
    @Override
    public TypeReference getTypeReferenceAt(int index) {
        if (returnType != null && index == 0) {
            return returnType;
        }
        throw new IndexOutOfBoundsException();
    }

    
    @Override
    public int getParameterDeclarationCount() {
        return (parameters != null) ? parameters.size() : 0;
    }

    
    @Override
    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (parameters != null) {
            return parameters.get(index);
        }
        throw new IndexOutOfBoundsException();
    }

    
    /**
     *      Get return type.
     *      @return the type reference.
     */
    public TypeReference getTypeReference() {
        return returnType;
    }
    
    
    public Comment[] getVoidComments() {
	return voidComments;
    }


    @Override    
    public final String getName() {
        return (name == null) ? null : name.toString();
    }


    public ImmutableArray<ParameterDeclaration> getParameters() {
        return parameters;
    }

    
    @Override    
    public String getFullName() {
	return getName();
    }


    public Throws getThrown() {
        return exceptions;
    }


    public StatementBlock getBody() {
        return body;
    }


    @Override
    public boolean isFinal() {
        return super.isFinal();
    }

    
    @Override
    public boolean isPrivate() {
        return super.isPrivate();
    }

    
    @Override    
    public boolean isProtected() {
        return super.isProtected();
    }

    
    /**
     * Test whether the declaration is public. Methods of interfaces
     * are always public.
     */
    @Override
    public boolean isPublic() {
        return parentIsInterfaceDeclaration || super.isPublic();
    }

    
    @Override
    public boolean isStatic() {
        return super.isStatic();
    }

    
    @Override
    public boolean isModel() {
        return super.isModel();
    }
    
    
    /**
     * test whether the declaration is a method with a variable number of arguments (i.e. the ellipsis ...)
     * @return true iff so
     */
    public boolean isVarArgMethod() {
        if (parameters == null || parameters.size() == 0)
            return false;
        return parameters.get(parameters.size() - 1).isVarArg();
    }

    
    @Override
    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    
    /**
     * Test whether the declaration is abstract. Methods of interfaces
     * are always abstract.
     */
    @Override    
    public boolean isAbstract() {
        return  parentIsInterfaceDeclaration || super.isAbstract();
    }

    
    /**
     * Test whether the declaration is native. Constructors
     * are never native.
     */
    @Override
    public boolean isNative() {
        return super.isNative();
    }


    @Override
    public boolean isSynchronized() {
        return super.isSynchronized();
    }

    
    @Override
    public void visit(Visitor v) {
	v.performActionOnMethodDeclaration(this);
    }

    @Override    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMethodDeclaration(this);
    }
}
