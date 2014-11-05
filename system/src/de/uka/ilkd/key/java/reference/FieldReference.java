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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;


public class FieldReference extends VariableReference 
                            implements MemberReference, ReferenceSuffix, 
                            TypeReferenceContainer, ExpressionContainer {

    /**
     *      Reference prefix.
     */
    protected ReferencePrefix prefix;
    

    protected FieldReference() {
        prefix = null;
    }

    public FieldReference(ProgramVariable pv, ReferencePrefix prefix) {
        super(pv);
        initPrefix(pv, prefix);
    }

    private void initPrefix(ProgramVariable pv, ReferencePrefix prefix) {
        if (prefix == null && !pv.isStatic() && pv.isMember()) {
            this.prefix = new ThisReference();
        } else {
            this.prefix = prefix;
        }
    }

    public FieldReference(ExtList children, ReferencePrefix prefix) {
        super(children);
        initPrefix(getProgramVariable(), prefix);
    }


    public FieldReference(ProgramVariable pv, ReferencePrefix prefix, PositionInfo pi) {
        super(pv, pi);
        initPrefix(pv, prefix);

    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
    */
    public int getChildCount() {
        int result = 0;
        if (prefix != null) result++;
        if (variable   != null) result++;
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
        if (variable != null) {
            if (index == 0) return variable;
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

    /*
     * returns true if the reference prefix is an explicit or implicit 
     * this reference this field reference does not refer to a static field
     */
    public boolean referencesOwnInstanceField() {
        return (prefix == null || prefix instanceof ThisReference) &&
            !getProgramVariable().isStatic();
    }
    

    /**
     *      Set reference prefix.
     *      @author VK
     */
    public ReferencePrefix setReferencePrefix(ReferencePrefix rp) {
        return new FieldReference(variable,rp);
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

    public SourceElement getFirstElement() {
        return (prefix == null) ? variable : prefix.getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
       return (prefix == null) ? variable : prefix.getFirstElementIncludingBlocks();
    }

    /** pretty print */
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFieldReference(this);
    }



    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnFieldReference(this);
    }
    
    /** are there "dots" in the prefix? */
    public boolean isSingleDeref() {
        return prefix.getReferencePrefix()==null;
    }

}