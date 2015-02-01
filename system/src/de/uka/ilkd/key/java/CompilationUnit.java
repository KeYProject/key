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


import java.io.IOException;
import java.io.StringWriter;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclarationContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *    A node representing a single source file containing
 *    {@link TypeDeclaration}s and an optional {@link PackageSpecification}
 *    and an optional set of {@link Import}s. In Java, any source file
 *    may contain at most one public class type definition.
 *    This class is taken from COMPOST and changed so that it can be
 *    used as an immutable class
 */

public class CompilationUnit
 extends JavaNonTerminalProgramElement
 implements TypeDeclarationContainer, TypeScope {

    /**
     * Package spec.
     */

    protected final PackageSpecification packageSpec;

    /**
     * Imports.
     */

    protected final ImmutableArray<Import> imports;

    /**
     * Type declarations.
     */
    protected final ImmutableArray<TypeDeclaration> typeDeclarations;

    /** creates a compilation unit 
     * @param packageSpec a PackageSpecification (pck of this CU)
     * @param imports an array of Import (all it imports)
     * @param typeDeclarations an array of TypeDeclaration (the 
     * type declared in it)
     */
    public CompilationUnit(PackageSpecification packageSpec, Import[]
			   imports,
			   TypeDeclaration[] typeDeclarations)
    { 
	this.packageSpec=packageSpec;
	this.imports=new ImmutableArray<Import>(imports);
	this.typeDeclarations=new ImmutableArray<TypeDeclaration>(typeDeclarations);
    }


    /** creates a compilation unit 
     * @param children list with the children of this unit
     */
    public CompilationUnit(ExtList children) {
	super(children);
	packageSpec=children.get(PackageSpecification.class); 
	this.imports=new ImmutableArray<Import>(children.collect(Import.class));
	this.typeDeclarations=new
	    ImmutableArray<TypeDeclaration>(children.collect(TypeDeclaration.class)); 
    }
    

    public SourceElement getFirstElement() {
        return (getChildCount() > 0) ? getChildAt(0).getFirstElement() : this;
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
       return (getChildCount() > 0) ? getChildAt(0).getFirstElementIncludingBlocks() : this;
    }

    public SourceElement getLastElement() {
        return
	    typeDeclarations.get(typeDeclarations.size()-1);
    }

    /**
     *     Get name of the unit. The name is empty if no data location is set;
     *     otherwise, the name of the current data location is returned.
     *      @return the name of this compilation unit.
     *    
     */
    public String getName() {
        return ""; //(location == null) ? "" : location.toString();
    }

    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (packageSpec      != null) result++;
        if (imports      != null) result += imports.size();
        if (typeDeclarations != null) result += typeDeclarations.size();
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
        if (packageSpec != null) {
            if (index == 0) return packageSpec;
            index--;
        }
        if (imports != null) {
            len = imports.size();
            if (len > index) {
                return imports.get(index);
            }
            index -= len;
        }
        if (typeDeclarations != null) {
            return typeDeclarations.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get imports.
 *      @return the wrapped import array.
     */

    public ImmutableArray<Import> getImports() {
        return imports;
    }


    /**
 *      Get package specification.
 *      @return the package specification.
     */

    public PackageSpecification getPackageSpecification() {
        return packageSpec;
    }


    /**
 *      Get the number of type declarations in this container.
 *      @return the number of type declarations.
     */

    public int getTypeDeclarationCount() {
        return (typeDeclarations != null) ?
	    typeDeclarations.size() : 0; 
    }

    /*
      Return the type declaration at the specified index in this node's
      "virtual" type declaration array.
      @param index an index for a type declaration.
      @return the type declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (typeDeclarations != null) {
            return typeDeclarations.get(index);         
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get declarations.
     *      @return the wrapped array of type declarations .
     */
    public ImmutableArray<TypeDeclaration> getDeclarations() {
        return typeDeclarations;
    }

    /**
     * Gets the primary type declaration of the compilation unit.
     * The primary declaration is the first declaration of the unit,
     * or the single public declaration. If there is no unambiguous primary 
     * declaration, this method returns <CODE>null</CODE>.
     */

    public TypeDeclaration getPrimaryTypeDeclaration() {
        TypeDeclaration res = null;
	int s = typeDeclarations.size();
        for (int i = 0; i < s; i += 1) {
            TypeDeclaration t = typeDeclarations.get(i);
            if (t.isPublic()) {
                if (res == null || !res.isPublic()) {
                    res = t;
                } else {
                    res = null;
                    break;
                }
            } else {
                if (res == null) {
                    res = t;
                }
            }
        }
        return res;
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printCompilationUnit(this);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnCompilationUnit(this);
    }


    /** toString */
    public String toString() {
	StringWriter sw = new StringWriter();
	try {
	    PrettyPrinter pp=new PrettyPrinter(sw);
	    pp.setIndentationLevel(3);
	    prettyPrint(pp);
	} catch (IOException e) {
	    System.err.println("Pretty printing of compilation unit failed");
	    System.err.println("Due to " + e);
	    e.printStackTrace();
	}
	return sw.toString();
    }
}