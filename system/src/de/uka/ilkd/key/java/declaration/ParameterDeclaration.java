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
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Formal parameters require a VariableSpecificationList of size() <= 1
 *  (size() == 0 for abstract methods) without initializer (for Java).
 */
public class ParameterDeclaration extends VariableDeclaration {


    /**
     *   Var spec.
     */
    protected final ImmutableArray<VariableSpecification> varSpec;
    
    
    /**
     * flag to store whether this parameter is a the last arg in a method
     * declaration with variable number of arguments. false if not otherwise
     * set in the appropriate constructor.
     */
    private final boolean varArgParameter;

    
    /**
     *      Parameter declaration.
     */
    public ParameterDeclaration() {
	this.varSpec = null;
	this.varArgParameter = false;
    }

    
    /**
     * Parameter declaration.
     * @param mods a modifier array.
     * @param typeRef a type reference.
     * @param var the VariableSpecification belonging to this parameter declaration.
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * the parent is an InterfaceDeclaration
     * @param parameterIsVarArg true iff this the last parameter of a method with variable number
     * of arguments
     */
    public ParameterDeclaration(Modifier[] mods,
                                TypeReference typeRef,
                                VariableSpecification var,
                                boolean parentIsInterfaceDeclaration,
                                boolean parameterIsVarArg) {   
        super(mods,typeRef,parentIsInterfaceDeclaration);
        this.varSpec = new ImmutableArray<VariableSpecification>(var);
        this.varArgParameter = parameterIsVarArg;
    }

    
    /**
     * Parameter declaration.
     * @param mods a modifier array.
     * @param typeRef a type reference.
     * @param var the VariableSpecification belonging to this parameter declaration.
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * the parent is an InterfaceDeclaration 
     */
    public ParameterDeclaration(Modifier[] mods,
				TypeReference typeRef,
				VariableSpecification var,
				boolean parentIsInterfaceDeclaration) {  	
        this(mods, typeRef, var, parentIsInterfaceDeclaration, false);
    }
    

    /**
     * Parameter declaration.
     * @param children an ExtList of children. May contain:	
     *  a VariableSpecification (specifying the parameter)
     *  a TypeReference (as reference to the type of the declared variable)
     * 	several Modifier (taken as modifiers of the declaration), 
     * 	a Comment
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * the parent is an InterfaceDeclaration 
     * @param parameterIsVarArg true iff this the last parameter of a method with variable number
     * of arguments
     */
    public ParameterDeclaration(ExtList children, 
				boolean parentIsInterfaceDeclaration,
				boolean parameterIsVarArg) {
        super(children,parentIsInterfaceDeclaration);
	this.varSpec = new ImmutableArray<VariableSpecification>(children.get(VariableSpecification.class));
	this.varArgParameter = parameterIsVarArg;
    }


    public VariableSpecification getVariableSpecification() {
        return varSpec.get(0);
    }

    
    public ImmutableArray<VariableSpecification> getVariables() {
        return varSpec;
    }


    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (modArray != null) result += modArray.size();
        if (typeReference != null) result++;
        if (varSpec  != null) result++;
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
                return modArray.get(index);
            }
            index -= len;
        }
        if (typeReference != null) {
            if (index == 0) return typeReference;
            index--;
        }
        if (varSpec != null) {
            if (index == 0) return varSpec.get(0);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    
    /**
     * Parameters are never private.
     */
    public boolean isPrivate() {
        return false;
    }

    
    /**
     * Parameters are never protected.
     */
    public boolean isProtected() {
        return false;
    }

    
    /**
     * Parameters are never public.
     */

    public boolean isPublic() {
        return false;
    }
    
    
    /**
     * Parameters are never static.
     */
    public boolean isStatic() {
        return false;
    }

    
    /**
     * Parameters are never transient.
     */
    public boolean isTransient() {
        return false;
    }

    
    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnParameterDeclaration(this);
    }
    
    
    /**
     * returns true iff this parameter is the last in a method with 
     * a variable number of arguments.
     * @return true if the parameter is the last in a method with
     * a variable number of arguments
     */
    public boolean isVarArg() {
        return varArgParameter;
    }
}
