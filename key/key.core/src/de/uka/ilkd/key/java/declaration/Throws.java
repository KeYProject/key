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
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Throws.
 *  @author <TT>AutoDoc</TT>
 */

public class Throws extends JavaNonTerminalProgramElement
 implements TypeReferenceContainer {


    /**
     *      Exceptions.
     */
    protected final ImmutableArray<TypeReference> exceptions;

    /**
     *      Throws.
     */
    public Throws() {
	this.exceptions=null;
    }

    /**
     *      Throws.
     *      @param exception a type reference.
     */
    public Throws(TypeReference exception) {
	this.exceptions=new ImmutableArray<TypeReference>(exception); 
    }

    /**
     *      Throws.
     *      @param list a type reference array.
     */
    public Throws(TypeReference[] list) {
	this.exceptions = new ImmutableArray<TypeReference>(list); 
    }



    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * 	May contain:
     * 		several of TypeReference (as references to thrown exceptions), 
     * 		Comments
     */
    public Throws(ExtList children) {
	super(children);
	this.exceptions=new
	    ImmutableArray<TypeReference>(children.collect(TypeReference.class));  
    }

    public SourceElement getLastElement() {
        if (exceptions == null) {
            return this;
        }
        return exceptions.get(exceptions.size() - 1);
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (exceptions != null) result += exceptions.size();
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
        if (exceptions != null) {
            return exceptions.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    
    /**
     *      Get exceptions.
     *      @return the type reference mutable list.
     */
    public ImmutableArray<TypeReference> getExceptions() {
        return exceptions;
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (exceptions != null) ? exceptions.size() : 0;
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
        if (exceptions != null) {
            return exceptions.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnThrows(this);
    }


    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThrows(this);
    }
}