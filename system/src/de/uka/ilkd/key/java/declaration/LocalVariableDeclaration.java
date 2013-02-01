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
import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Local variable declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public class LocalVariableDeclaration
    extends VariableDeclaration implements LoopInitializer {


    /**
     *      Var specs.
     */

    protected final ImmutableArray<VariableSpecification> varSpecs;

    /**
     *      Local variable declaration.
     */

    public LocalVariableDeclaration() {
	super();
	this.varSpecs = null;
    }


    /**
     *      Local variable declaration.
     *      @param mods a modifier array.
     *      @param typeRef a type reference.
     *      @param vars a variable specification array.
     */
    public LocalVariableDeclaration(Modifier[] mods, TypeReference
				    typeRef, 
				    VariableSpecification[] vars) {  
	super(mods,typeRef,false);
	this.varSpecs=new
	    ImmutableArray<VariableSpecification>(vars); 
    }

    /**
     *      Local variable declaration which declared exactly 
     *      one variable.
     *      @param typeRef a type reference.
     *      @param var the variable specification
     */
    public LocalVariableDeclaration(TypeReference typeRef, 
				    VariableSpecification var) {  
	this(new ImmutableArray<Modifier>(new Modifier[0]),typeRef,var);
    }


    /**
     *      Local variable declaration.
     *      @param mods a modifier array.
     *      @param typeRef a type reference.
     *      @param var a variable specification .
     */
    public LocalVariableDeclaration(ImmutableArray<Modifier> mods, TypeReference
				    typeRef, VariableSpecification var) {  
	super(mods,typeRef,false);
	this.varSpecs = new ImmutableArray<VariableSpecification>(var); 
    }

    /**
     *      Local variable declaration.
     *      @param mods a modifier array.
     *      @param typeRef a type reference.
     *      @param vars a variable specification array.
     */
    public LocalVariableDeclaration(ImmutableArray<Modifier> mods, TypeReference
				    typeRef, VariableSpecification[] vars) {  
	super(mods,typeRef,false);
	this.varSpecs = new ImmutableArray<VariableSpecification>(vars); 
    }


    /**
     * Local variable declaration. 
     * @param children an ExtList containing the children. May include: 
     *  several VariableSpecification (specifying the declared local variable),
     * 	a TypeReference (as reference to the type of the declared variable),
     * 	several Modifier (taken as modifiers of the declaration), 
     * 	a Comment
     */

    public LocalVariableDeclaration(ExtList children) {
        super(children, false);
        
	this.varSpecs = new
	    ImmutableArray<VariableSpecification>(children.collect(VariableSpecification.class));
    }

    /**
     * This method is identical to {@link #getVariables()}.
     */
    public ImmutableArray<VariableSpecification> getVariableSpecifications() {
        return varSpecs;
    }

    /**
     * This method is identical to {@link #getVariableSpecifications()}.
     */
    public ImmutableArray<VariableSpecification> getVariables() {
        return varSpecs;
    }

    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (modArray     != null) result += modArray.size();
        if (typeReference != null) result++;
        if (varSpecs      != null) result += varSpecs.size();
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
        if (varSpecs != null) {
            return varSpecs.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Local variables are never private.
     */

    public boolean isPrivate() {
        return false;
    }

    /**
     * Local variables are never protected..
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Local variables are never "public".
     */

    public boolean isPublic() {
        return false;
    }

    /**
     * Local variables are never static.
     */

    public boolean isStatic() {
        return false;
    }

    /**
     * Local variables are never transient.
     */

    public boolean isTransient() {
        return false;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnLocalVariableDeclaration(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printLocalVariableDeclaration(this);
    }

}
