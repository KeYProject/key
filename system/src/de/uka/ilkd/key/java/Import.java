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

package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Import.
 * 
 */
public class Import extends JavaNonTerminalProgramElement
 implements TypeReferenceContainer, PackageReferenceContainer {

    /**
     *        Multi import flag.
     */

    protected final boolean isMultiImport;


    /**
     *      Type reference infix.
     */
    protected final TypeReferenceInfix reference;
    
    /**
     * children may contain: TypeReference (for import), a Comment
     * @param isMultiImport indicates whether the import contains multiple 
     * imports
     */
    public Import(ExtList children, boolean isMultiImport) {
	super(children);
	reference=children.get(TypeReferenceInfix.class);
	this.isMultiImport=isMultiImport;
    }


    /**
     *      Import.
     */
    public Import() {
	isMultiImport=false;
	reference=null;
    }

    /**
     *      Import.
     *      @param t a type reference.
     *      @param multi indicates the wildcard.
     */
    public Import(TypeReference t, boolean multi) {
        reference=t;
        isMultiImport=multi;
    }

    /**
     *      Import.
     *      @param t a package reference.
     */

    public Import(PackageReference t) {
       reference=t;
       isMultiImport=true;
    }

    public SourceElement getLastElement() {
        return reference;
    }

    /**
     *        Checks if this import is a multi type import, also known as
     *        type-on-demand import.
     *        @return the kind of this import.
     */

    public boolean isMultiImport() {
        return isMultiImport;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
    */
    public int getChildCount() {
        int result = 0;
        if (reference != null) result++;
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
        if (reference != null) {
            if (index == 0) return reference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (reference instanceof TypeReference) ? 1 : 0;
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
        if (reference instanceof TypeReference && index == 0) {
            return (TypeReference)reference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *        Returns the type reference of this import, if there is one.
     *        @return the reference of this import statement.
    */

    public TypeReference getTypeReference() {
        return (reference instanceof TypeReference) 
	    ? (TypeReference)reference : null;
    }

    /**
     *        Returns the package reference of this import, if there is one.
     *        @return the reference of this import statement.
    */

    public PackageReference getPackageReference() {
        return (reference instanceof PackageReference) ? 
	    (PackageReference)reference : null;
    }

    /**
     *        Returns the reference of this import, either a
     *        type or a package reference.
     *        @return the reference of this import statement.
    */

    public TypeReferenceInfix getReference() {
        return reference;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnImport(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printImport(this);
    }
}