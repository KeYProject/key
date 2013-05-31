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


package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;
/**
 * KeY used to model arrays using only the {@link
 * de.uka.ilkd.key.java.abstraction.ArrayType}. As the only attribute of
 * an array has been the length attribute, it has been handled in a
 * different way than members of usual classes. As we need some implicit
 * fields for array creation and initialisation, the special handling of
 * arrays is not any longer practicable. 
 *  So, this class introduce a 'virtual' declaration for array types
 * containing all required members. Please not the array fields accessed
 * by an index are not included, so arrays of different lengths with same base
 * type belong to the same array declaration.
 * Attention: In contrast to the other type declaration, array
 * declarations may be added at runtime.
 */

public class ArrayDeclaration 
    extends TypeDeclaration implements ArrayType {


    /** 
     * reference to the type the elements of this array must subclass
     */
    private final TypeReference basetype;

    /**
     * dimension of the array 
     */
    private final int dim;

    private final KeYJavaType superType;

    private String altNameRepresentation;

    private ArrayDeclaration(ExtList children, 
			     TypeReference baseType,
			     ProgramElementName name,
			     KeYJavaType superType) { 	
	super(addLength(children, superType), name, name, false);
	assert name != null;
	this.basetype  = baseType;
	this.dim       = dimension();
	this.superType = superType;
    }

    private static ExtList addLength(ExtList children, KeYJavaType superType) {
	children.add(((SuperArrayDeclaration)superType.getJavaType()).length());
	return children;
    }

    /**
     * ArrayDeclaration
     * @param children an ExtList with the basetype and member
     * declarations of this type
     */
    public ArrayDeclaration(ExtList children, 
			    TypeReference baseType,
			    KeYJavaType superType) { 	
	this(children, baseType, createName(baseType), superType);
    } 

    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (modArray != null) result += modArray.size();
        if (name     != null) result ++;
	if (basetype != null) result ++;
        if (members  != null) result += members.size();
        return result;
    }

    public FieldDeclaration length() {
	return ((SuperArrayDeclaration)superType.getJavaType()).length();
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *    of bounds
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
        if (name != null) {
            if (index == 0) return name;
            index--;
        }
        if (basetype != null) {
            if (index == 0) return basetype;
            index--;
        }
        if (members != null) {
            return members.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the element/base type.
     * @return refernce to the base type .
     */
    public TypeReference getBaseType() {
        return basetype;
    }

    /**
     * Arrays are never strictfp.
     */
    public boolean isStrictFp() {
        return false;
    }

    /**
     * Arrays are never transient.
     */
    public boolean isTransient() {
        return false;
    }

    /**
     * Arrays are never volatile.
     */
    public boolean isVolatile() {
        return false;
    }

    /**
     * Arrays are never interfaces (but may have interface types as
     * element types)
     */
    public boolean isInterface() {
        return false;
    }
    
    /**
     * return the dimension of this array
     */
    public int getDimension() {
	return dim;
    }

    /** 
     * returns the default value of the given type 
     * according to JLS Sect. 4.5.5
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
     */
    public Literal getDefaultValue() {
	return NullLiteral.NULL;
    }

    /**
     * computes the dimension of this array
     */
    private int dimension() {
	Type javaType = basetype.getKeYJavaType().getJavaType(); 
	if (javaType instanceof ArrayType) {
	    return 1+((ArrayType)javaType).getDimension();
	} else {
	    return 1;
	}
    }

    public static ProgramElementName createName(TypeReference basetype) {

	Type javaBasetype = basetype.getKeYJavaType().getJavaType();
	
	if (javaBasetype == null) {
	    // entered only if base type is class type
	    return new ProgramElementName
		("[L"+basetype.getName());
	    
	}
	if(javaBasetype instanceof ArrayDeclaration){
	    return new ProgramElementName
		("["+ javaBasetype.getFullName());
	} else if (javaBasetype instanceof TypeDeclaration) {
	    return new ProgramElementName("[L"+javaBasetype.getFullName());
	} else if (javaBasetype instanceof PrimitiveType) {
	    return ((PrimitiveType)javaBasetype).getArrayElementName();
	} 
	assert false;
	return null;
    }


    public String getAlternativeNameRepresentation() {
        if (altNameRepresentation == null) {
            final StringBuffer alt = new StringBuffer();            
            Type baseType = basetype.getKeYJavaType().getJavaType();
            
            if (baseType instanceof ArrayType) {
                alt.append(((ArrayType) baseType).
                        getAlternativeNameRepresentation());                
            } else {
                if (baseType instanceof ClassType) {
                    alt.append(baseType.getFullName());
                } else {                   
                    alt.append(baseType.getName());
                }
            }        
            alt.append("[]");
            altNameRepresentation = alt.toString();
        }
        return altNameRepresentation;
    }
    

    /** 
     * returns the local declared supertypes
     */
    public ImmutableList<KeYJavaType> getSupertypes() {
	return ImmutableSLList.<KeYJavaType>nil().append(superType);
    }

    /** 
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnArrayDeclaration(this);
    }

    /**
     * pretty prints an array declaration
     */
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printArrayDeclaration(this);
    }

    /**
     * toString
     */
    public String toString() {
	return name.toString().intern();
    }

}

