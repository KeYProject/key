// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

/** 
 * this class is used to represent the reference operator '.' of
 * Java, e.g.>> int[] a = new int[]{1,2,3};  int i = a.length; <<<
 * where the '.' in a.length points to field called length
 * ATTENTION: At this moment only variables are adressed to this may
 * change in future
 */
public class AttributeOp extends AccessOp {

    /** 
     * The pool of already created attribute operators. Ensures
     * 'singleton' property of attribute operators.
     */
    private static final WeakHashMap operatorPool = new WeakHashMap(50);
    
    /** The attribute, which is accessed via this operator */
    private final IProgramVariable attribute;

    /** Sort of the program variables */
    private final Sort sort;

    /** 
     * returns and if neccessary creates the access operator of the
     * given attribute 
     * @return the attribute operator for the given attribute
     */
    public static AttributeOp getAttributeOp(IProgramVariable attribute) { 
	WeakReference attributeOpReference = 
	    (WeakReference) operatorPool.get(attribute);
	if (attributeOpReference == null || attributeOpReference.get() == null) {
	    // wrapping attributeOp in a weak reference is necessary as
	    // it contains a strong reference to its key
	    attributeOpReference = new WeakReference(new AttributeOp(attribute));
	    operatorPool.put(attribute, attributeOpReference);	    
	} 
	return (AttributeOp)attributeOpReference.get();
    }
    
    /** 
     * creates a new access operator for the given attribute
     * @param attribute the ProgramVariable representing a field
     */
    protected AttributeOp(IProgramVariable attribute) {
	super(new Name("." + attribute.name().toString()));
	this.attribute = attribute;
	this.sort = attribute  instanceof ProgramSV ? 
	    attribute.sort() : attribute.sort();
    }

    /**
     * checks whether the top level structure of the given {@link Term}
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	if (((AttributeOp)term.op()).attribute() instanceof SchemaVariable ||
	    term.sub(0).op() instanceof SchemaVariable ||
	    term.sub(0).sort() == AbstractMetaOperator.METASORT) {
	    return true;
	} else if (term.arity() != arity()) {
	    return false;
	}
    return term.sub(0).sort() instanceof ObjectSort
	   || term.sub(0).sort() instanceof ArraySort;
    }

    /**
     * The arity of an attribute operator is <code>1</code> and the
     * corresponding subterm denotes the object whose attribute is
     * accessed.
     * @return arity of the Operator as int 
     */
    public int arity(){
        return 1;
    }

    /** returns the attribute of the operator 
     * @return  the attribute of the operator 
     */
    public IProgramVariable attribute() {
	return attribute;
    }
    
    /**
     * returns the KeYJavaType the attribute is declared in
     */
    public KeYJavaType getContainerType() {
        return ((ProgramVariable)attribute()).getContainerType();
    }
    
    /** 
     * the sort of the attribute
     */
    public Sort sort() {
        return attribute.sort();
    }

    /** 
     * returns the {@link KeYJavaType} of this access operator
     * @return the KeYJavaType of this access operator
     */
    public KeYJavaType getKeYJavaType(Term t) {
	return attribute.getKeYJavaType();
    }

    /**
     * the top level operator of t must be <tt>this</tt>
     * returns the reference prefix of this attribute of the given term
     */
    public Term referencePrefix(Term t) {
        Debug.assertTrue(t.op() == this);
        return t.sub(0);
    }
    
    /**
     * converts the logical attribute access operator to its Java
     * dependance
     */
    public Expression convertToProgram(Term t, de.uka.ilkd.key.util.ExtList l) {
	return new FieldReference((ProgramVariable) attribute, 
				  (ReferencePrefix)l.get(0));
    }

    /**
     * determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param term an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    public Sort sort(Term[] term) {
	return sort;
    }


    /**
     * @return true if the operator is a shadowed 
     */
    public boolean isShadowed() {
	return false;
    }

    public boolean equals(Object o) {
	return o == this;
    }

    public int hashCode() {
	return AttributeOp.class.hashCode() + 
	    17 * attribute.hashCode();
    }

    /** toString */
    public String toString() {
	return name().toString();
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Location#mayBeAliased(de.uka.ilkd.key.logic.op.Location)
     */
    public boolean mayBeAliasedBy(Location loc) {
        return (loc == this || 
                (loc instanceof AttributeOp && 
                 !((AttributeOp)loc).isShadowed() &&
                 (attribute instanceof SortedSchemaVariable ||
                  (((AttributeOp)loc).attribute 
                          instanceof SortedSchemaVariable))));                  
    }
    
    
    
    /**
     * Tries to match the given operator <code>op</code> with this one.
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst == this) return mc;
        if (subst.getClass() != this.getClass()) {
            Debug.out("FAILED. Operator mismatch (template, orig)", this, subst);
            return null;
        }      
        final AttributeOp attrOp = (AttributeOp)subst;
        return attribute.match(attrOp.attribute, mc, services);
    }
} 
