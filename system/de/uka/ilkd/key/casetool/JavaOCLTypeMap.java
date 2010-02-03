// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool;

import tudresden.ocl.check.OclTypeException;
import tudresden.ocl.check.types.Any;
import tudresden.ocl.check.types.Basic;
import tudresden.ocl.check.types.Type;

/**
 * @deprecated
 */
public class JavaOCLTypeMap {

    protected HashMapOfClassifier classes;

    private static final Type[] basicTypes
	= new Type[]{Basic.INTEGER, Basic.REAL, Basic.BOOLEAN};

    public static final Type[] getBasicTypes() {
	return basicTypes;
    }

    private JavaOCLTypeMap() {
    }

    public JavaOCLTypeMap(HashMapOfClassifier cls) {
	this.classes = cls;
    }

    public static Type getBasicTypeFor(String t) {
	if (t.equals("byte") || t.equals("short") || 
	    t.equals("char") || t.equals("int")  || 
	    t.equals("long")) {
	    return Basic.INTEGER;
	} else if (t.equals("float") || t.equals("double")) {
	    return Basic.REAL;
	} else if (t.equals("boolean")) {
	    return Basic.BOOLEAN;
	} else if (t.equals("void")) {
	    return Any.VOID;
	} else
	    throw new OclTypeException("Cannot find OCL type"+
				       "for Java type \""+t+"\"");
    }
    
    private boolean isBasicType(recoder.abstraction.Type type){
	if ((type instanceof recoder.abstraction.PrimitiveType)
	    || (type instanceof recoder.abstraction.NullType)) {
	    //???            || (type == null)) {
	    return true;
	} else  {
	    return false;
	}
    }
    
    public Type getTypeFor(recoder.abstraction.Type type, 
			   HashMapOfClassifier classes){
        if (type == null) {
	    return getBasicTypeFor("void");
        } else if (isBasicType(type)) {
	    // basic type
	    return getBasicTypeFor(type.getName());
	} else if ("java.lang.String".equals(type.getFullName())) {
	    return Basic.STRING;
	} else {
	    String refClass = type.getName();
	    if (classes.getClassifier(refClass) != null 
		&& refClass!=null) {
		return classes.getClassifier(refClass);
	    }
	    else {
		return null;
		//		return new UMLOCLClassifier(type.getFullName());
            }
        }
    }

    public String toString() {
	return classes.toString();
    }
    
}
