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

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Field declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public class FieldDeclaration extends VariableDeclaration implements MemberDeclaration {


    /**
     *      Field specs.
     */

    protected final ImmutableArray<FieldSpecification> fieldSpecs;

    /**
     *      Field declaration.
     *      @param mods a modifier mutable list.
     *      @param typeRef a type reference.
     *      @param vars a variable specification array.
     *      @param parentIsInterfaceDeclaration a boolean set true 
     * iff parent is an InterfaceDeclaration
     */

    public FieldDeclaration(Modifier[] mods, TypeReference typeRef,
			    FieldSpecification[] vars, 
			    boolean parentIsInterfaceDeclaration) { 
        super(mods,typeRef,parentIsInterfaceDeclaration);	
	fieldSpecs = new
	    ImmutableArray<FieldSpecification>(vars); 
    }

    /**
     *      Field declaration.
     *  @param children an ExtList of children. May include:
     * 	several FieldSpecification (for the field)
     * 	a TypeReference (as reference to the type of the declared variable)
     * 	several Modifier (taken as modifiers of the declaration), 
     * 	a Comment
     *      @param parentIsInterfaceDeclaration a boolean set true 
     */
    public FieldDeclaration(ExtList children, 
			    boolean parentIsInterfaceDeclaration) {
        super(children, parentIsInterfaceDeclaration);
	fieldSpecs = new
	    ImmutableArray<FieldSpecification>(children.collect(FieldSpecification.class));
    }
    
    public ImmutableArray<FieldSpecification> getFieldSpecifications() {
        return fieldSpecs;
    }

    public ImmutableArray<? extends VariableSpecification> getVariables() {
        return fieldSpecs;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (modArray     != null) result += modArray.size();
        if (typeReference != null) result++;
        if (fieldSpecs    != null) result += fieldSpecs.size();
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
        if (fieldSpecs != null) {
            return fieldSpecs.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Test whether the declaration is final. Fields of interfaces are
     * always final.
     */

    public boolean isFinal() {
        return parentIsInterfaceDeclaration || super.isFinal();
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
     * Test whether the declaration is public. Fields of interfaces
     * are always public.
     */

    public boolean isPublic() {
        return parentIsInterfaceDeclaration || super.isPublic();
    }

    /* *
     * Test whether the declaration is static.
     */
    public boolean isStatic() {
//        return parentIsInterfaceDeclaration || super.isStatic();
     // DB 2012-05-08: interfaces may contain non-static model fields
        return super.isStatic();
    }

    /**
     * Test whether the declaration is transient.
     */

    public boolean isTransient() {
        return !parentIsInterfaceDeclaration && super.isTransient();
    }

    /**
     * Test whether the declaration is strict FP.
     */

    public boolean isStrictFp() {
        return super.isStrictFp();
    }
    
    /**
     * Test whether the declaration is model (the jml modifier is meant).
     */

    public boolean isModel() {
        return super.isModel();
    }

    /**
     * Test whether the declaration is ghost (the jml modifier is meant).
     */

    public boolean isGhost() {
        return super.isGhost();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnFieldDeclaration(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFieldDeclaration(this);
    }
}