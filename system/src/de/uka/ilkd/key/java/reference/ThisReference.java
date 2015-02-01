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

package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  A reference to the current object.
 *  "this" can be prefixed by a type reference (to resolve ambiguities
 *  with inner classes).
 */

public class ThisReference
 extends JavaNonTerminalProgramElement
 implements Reference, Expression, ReferencePrefix, ReferenceSuffix, TypeReferenceContainer {
    
    /**
     *      Prefix.
     */
    private final ReferencePrefix prefix;



    /**
     *      This reference.
     */
    public ThisReference() {
	prefix    = null;
    }

    /**
     *      This reference.
     *      @param outer a type reference.
     */
    public ThisReference(TypeReference outer) {
	prefix    = outer;
    }

   /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: 
     * 	a TypeReference (as reference for the ThisReference)
     *  Comments
     */ 
    public ThisReference(ExtList children) {
	super(children);
	prefix = children.get(TypeReference.class);
    }


    public SourceElement getFirstElement() {
        return (prefix == null) ? this : prefix.getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return (prefix == null) ? this : prefix.getFirstElementIncludingBlocks();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
	int count = 0;
	if (prefix != null) count++;
        return count;
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
        if (prefix != null) {
            if (index == 0) return prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get reference prefix.
     *      @return the reference prefix.
     */
    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (prefix != null) ? 1 : 0;
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
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference)prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnThisReference(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThisReference(this);
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }    

    public KeYJavaType getKeYJavaType(Services javaServ, 
				      ExecutionContext ec) {
	return ec.getTypeReference().getKeYJavaType();
    }

}