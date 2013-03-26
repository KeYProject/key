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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Field reference.
 *  @author <TT>AutoDoc</TT>
 */
public class SchematicFieldReference extends FieldReference 
                            implements MemberReference, ReferenceSuffix, 
                            TypeReferenceContainer, ExpressionContainer {

    /**
     * Reference suffix
     */
     protected final SchemaVariable schemaVariable;


    public SchematicFieldReference(SchemaVariable pe, ReferencePrefix prefix) {
	this.schemaVariable = pe;
	this.prefix = prefix;
    }


    public SchematicFieldReference(ExtList children, ReferencePrefix prefix) {
	this.schemaVariable = children.get(SchemaVariable.class);
	this.prefix   = prefix;
    }


    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (prefix   != null) result++;
        if (schemaVariable != null) result++;
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
        if (schemaVariable != null) {
            if (index == 0) return (ProgramSV)schemaVariable;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get reference prefix.
     * @return the reference prefix.
     */
    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     * Get reference prefix.
     * @return the reference prefix.
     */
    public ReferenceSuffix getReferenceSuffix() {
        return (ProgramSV)schemaVariable;
    }


    /**
     *      Set reference prefix.
     *      @author VK
     */
    public ReferencePrefix setReferencePrefix(ReferencePrefix rp) {
	return new SchematicFieldReference(schemaVariable, rp);
    }


    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (prefix instanceof TypeReference) ? 1 : 0;
    }

    /**
     * Return the type reference at the specified index in this node's
     * "virtual" type reference array.
     * @param index an index for a type reference.
     * @return the type reference with the given index.
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *   of bounds.
     */
    public TypeReference getTypeReferenceAt(int index) {
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference)prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (prefix instanceof Expression) ? 1 : 0;
    }

    /**
     *  Return the expression at the specified index in this node's
     *  "virtual" expression array.
     *  @param index an index for an expression.
     *  @return the expression with the given index.
     *  @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *   of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression && index == 0) {
            return (Expression)prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? (ProgramSV)schemaVariable : prefix.getFirstElement();
    }

    public ProgramElementName getProgramElementName() {
	return (ProgramElementName) schemaVariable.name();
    }

    /** 
     * pretty print 
     */
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFieldReference(this);
    }

    /** 
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnSchematicFieldReference(this);
    }


    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        ProgramElement src = source.getSource();
        if (!(src instanceof FieldReference)) {
            Debug.out("Program match failed. SchematicFieldReferences matches only FieldReferences (pattern, source)",
                    this, src);
            return null;
        }
        
        final SourceData newSource = new SourceData(src, 0, source.getServices());
        
        matchCond = super.matchChildren(newSource, matchCond, 0);
        
        if (matchCond == null) {
            return null;
        }
        source.next();
        return matchCond;
    }
    
}
