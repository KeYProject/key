// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;

public class ExecutionContext
    extends JavaNonTerminalProgramElement 
    implements Reference, TypeReferenceContainer, 
	       ExpressionContainer {
    
    /**
     * the ast parent
     */
    private NonTerminalProgramElement astParent;

    /**
     * the class context 
     */
    private TypeReference classContext;
    
    /**
     * the reference to the active object
     */
    private ReferencePrefix runtimeInstance;
    
    /**
     * the outer execution context of this context
     */
    private ExecutionContext parent;

    protected ExecutionContext() {}

    /**
     * creates an execution context reference
     * @param classContext the TypeReference refering to the next enclosing
     * class 
     * @param runtimeInstance a ReferencePrefix to the object that
     * is currently active/executed
     * @param parent the outer execution context of this
     */
    public ExecutionContext(TypeReference classContext, 
			    ReferencePrefix runtimeInstance,
			    ExecutionContext parent) {
	this.classContext = classContext;
	this.runtimeInstance  = runtimeInstance;
	this.parent = parent;
	makeParentRoleValid();
    }
    
    /**
     * creates an execution context reference
     * @param classContext the TypeReference refering to the next enclosing
     * class 
     * @param runtimeInstance a ReferencePrefix to the object that
     * is currently active/executed
     */
    public ExecutionContext(TypeReference classContext, 
                            ReferencePrefix runtimeInstance) {
        this(classContext, runtimeInstance, null);
    }


    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
	int count = 0;
	if (runtimeInstance != null) count++;
	if (classContext != null) count++;
	if (parent != null) count++;
	return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array.
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *    of bounds
     */
    public ProgramElement getChildAt(int index) {
	if (classContext != null) {
	    if (index == 0) return classContext;
	    index--;
	}
	if (runtimeInstance != null) {
	    if (index == 0) return runtimeInstance;
	    index--;
	}
	if (parent != null) {
	    if (index == 0) return parent;
	    index--;
	}
	throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Returns the positional code of the given child
     * @param child the exact child to look for.
     * @return the positional code of the given child, or <CODE>-1</CODE>.
     */
    public int getChildPositionCode(ProgramElement child) {
	if (child != null) {
	    if (child == classContext) return 0;
	}
	if (runtimeInstance != null) {
	    if (child == runtimeInstance) return (1 << 4 | 1);
	}
	if (parent != null) {
	    if (child == parent) return (1 << 5 | 1);
	}
	return -1;
    }

    public void accept(SourceVisitor visitor) {       
    }

    public Object deepClone() {
	return new ExecutionContext(classContext, runtimeInstance, parent);
    }

    public NonTerminalProgramElement getASTParent() {
	return astParent;
    }

    public void setParent(NonTerminalProgramElement parent) {
	astParent = parent;
    }

    public boolean replaceChild(recoder.java.ProgramElement child, 
				recoder.java.ProgramElement newChild) {
	if (child == classContext) {
	    classContext = (TypeReference) newChild;
	} else if (child == runtimeInstance) {
	    runtimeInstance = (ReferencePrefix)newChild;
	} else if (child == parent) {
            parent = (ExecutionContext)newChild;
        } else {
	    return false;
	}
	makeParentRoleValid();
	return true;
    }
    
    /**
     *      Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (classContext != null) {
            classContext.setParent(this);            
        }
        if (runtimeInstance != null) {
            ((Expression)runtimeInstance).setExpressionContainer(this);
        }
    }
    
    
    public TypeReference getTypeReferenceAt(int index) {
	if (classContext != null && index == 0) {
	    return classContext;
	}
	throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
	return classContext == null ? 0 : 1;    
    }



    public Expression getExpressionAt(int index) {
	if (runtimeInstance != null && index == 0) {
	    return (Expression) runtimeInstance;
	}
	throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
	return runtimeInstance == null ? 0 : 1;    
    }


    /**
     * returns the type reference to the next enclosing class
     * @return the type reference to the next enclosing class
     */
    public TypeReference getTypeReference() {
	return classContext;
    }
    
    public ExecutionContext getParent(){
        return parent;
    }
    

    /**
     * returns the runtime instance object
     * @return the runtime instance object
     */
    public ReferencePrefix getRuntimeInstance() {
	return runtimeInstance;
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
    }
}
