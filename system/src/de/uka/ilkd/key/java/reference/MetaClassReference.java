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



package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Meta class reference.
 *  
 */

public class MetaClassReference extends JavaNonTerminalProgramElement
    implements Reference, Expression, ReferencePrefix, ReferenceSuffix,
    TypeReferenceContainer {

    /**
     *      Type reference.
     */
    protected final TypeReference typeReference;

    /**
     *      Meta class reference.
     */
    public MetaClassReference() {
	typeReference=null;
    }

    /**
     *      Meta class reference.
     *      @param reference a type reference.
     */
    public MetaClassReference(TypeReference reference) {
        typeReference=reference;
    }
    
    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain:
     * a TypeReference (as reference for the meta class),
     * Comments
     */ 
    public MetaClassReference(ExtList children) {
	super(children);
	typeReference=children.get(TypeReference.class);
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return  (typeReference != null) ? 1 : 0;
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
        if (typeReference != null) {
            if (index == 0) return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get reference prefix.
     *      @return the reference prefix.
     */
    public ReferencePrefix getReferencePrefix() {
        return typeReference;
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (typeReference != null) ? 1 : 0;
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
        if (typeReference != null && index == 0) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get type reference.
     *      @return the type reference.
     */
    public TypeReference getTypeReference() {
        return typeReference;
    }

    public SourceElement getFirstElement() {
        return (typeReference == null) ? 
	    this : typeReference.getFirstElement();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnMetaClassReference(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMetaClassReference(this);
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }


    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	throw new IllegalStateException
	    ("Metaclass references are not supported by KeY as" + 
	     "\'java.lang.Class\' is not part of the Java Card standard");
    }

}
