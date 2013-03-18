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
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.ExtList;
/**
 *  TypeReferences reference {@link recoder.abstraction.Type}s by name.
 *  A TypeReference can refer to an outer or inner type and hence can also
 *  be a {@link MemberReference}, but does not have to.
 *  A TypeReference can also occur as part of a reference path and
 *  as a prefix for types, too. As a possible suffix for types, it can
 *  have other TypeReferences as a prefix, playing the role of a
 *  {@link TypeReferenceContainer}.
 */

public abstract class TypeReferenceImp
 extends JavaNonTerminalProgramElement
 implements TypeReference {


    /**
     *      Prefix.
     */
    protected ReferencePrefix prefix;

    /**
     *      Dimensions.
     */
    protected int dimensions;

    /**
     *      Name.
     */
    protected ProgramElementName name;


    /**
     * Constructor for the transformation of RECODER ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: 
     * 	a ReferencePrefix (as prefix of the type reference)
     *  a ProgramElementName (as name for the type reference)
     *  Comments
     * @param dim the dimension of this type
     */
    public TypeReferenceImp(ExtList children, int dim) {
	super(children);
	prefix = children.get(ReferencePrefix.class);
	name = children.get(ProgramElementName.class);
	dimensions = dim;
    }


    public TypeReferenceImp(ProgramElementName name) {	
	this(name, 0, null);
    }

    public TypeReferenceImp(ProgramElementName name, 
			    int dimension, 
			    ReferencePrefix prefix) {
	this.name = name;
	this.dimensions = dimension;
	this.prefix = prefix;
    }


    public SourceElement getFirstElement() {
        return (prefix == null) ? name : prefix.getFirstElement();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (prefix != null) result++;
        if (name   != null) result++;
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
        if (prefix != null) {
            if (index == 0) return prefix;
            index--;
        }
        if (name != null) {
            if (index == 0) return name;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (prefix instanceof TypeReference) ? 1 : 0;
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

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */
    public int getExpressionCount() {
        return (prefix instanceof Expression) ? 1 : 0;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression && index == 0) {
            return (Expression)prefix;
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
     *      Get the package reference.
     *      @return the package reference.
     */
    public PackageReference getPackageReference() {
        return (prefix instanceof PackageReference) 
	    ? (PackageReference)prefix : null;
    }
    
    /**
     *      Get dimensions.
     *      @return the int value.
     */
    public int getDimensions() {
        return dimensions;
    }

    /**
     *      Get name.
     *      @return the string.
     */
    public final String getName() {
        return (name == null) ? null : name.toString();
    }

    public abstract KeYJavaType getKeYJavaType();

    /**
     *      Get identifier.
     *      @return the identifier.
     */

    public ProgramElementName getProgramElementName() {
        return name;
    }

    
    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnTypeReference(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printTypeReference(this);
    }


    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement pe = source.getSource(); 
        if (!(pe instanceof TypeReference) || ((TypeReference)pe).getDimensions() != getDimensions()) {
            return null;
        } 
        
        return super.match(source, matchCond);
    }
}
