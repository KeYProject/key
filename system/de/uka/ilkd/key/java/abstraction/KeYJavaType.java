// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.abstraction;

import java.util.Comparator;

import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.*;

/**
 * The KeY java type realises a tuple (sort, type) of a logic sort and
 * the java type (for example a class declaration). 
 * In contrast to other classes the KeYJavaType is <emph>not</emph>
 * immutable, so use it with care. 
 */
public class KeYJavaType implements Type {


    /** the AST type */
    private Type javaType=null;
    /** the logic sort */
    private Sort sort=null;
    
    /** creates a new KeYJavaType */
    public KeYJavaType() {
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Type javaType, Sort sort) {
	this.javaType = javaType;
	this.sort = sort;
        ensureTypeSortConformance();
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Sort sort) {
	this.sort = sort;
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Type type) {
	this.javaType = type;
    }
    
    private void ensureTypeSortConformance() {
        if (javaType != null && sort != null) {
            
            if (javaType instanceof NullType && sort instanceof NullSort) {
                return;
            }
            
            final boolean b = 
                (javaType instanceof ClassType ==  sort instanceof ObjectSort);
            
            if (!b) {
                throw new IllegalStateException("A primitive sort/type cannot be mapped " +
                        "for a reference type/sort (type:" + javaType + "," 
                        +sort+")");
            }
                                    
            boolean arrayTypeSort = 
                (javaType instanceof ArrayType ==  sort instanceof ArraySort); 
            
            if (!arrayTypeSort) {
                throw new IllegalStateException("A non-array sort/type cannot be mapped " +
                        "to an array type/sort (type:" + javaType + "," 
                        +sort+")");
            }
            
            if (javaType instanceof ClassType) {                   
                final ObjectSort os = (ObjectSort)sort;
                if (os instanceof ClassInstanceSort) {
                    boolean conform = 
                        ((ClassInstanceSort)os).representAbstractClassOrInterface() ==
                            (((ClassType)javaType).isAbstract() || 
                                    ((ClassType)javaType).isInterface());
                    if (!conform) {
                        throw new IllegalStateException("Java type " + javaType 
                                + " cannot be mapped to sort " + os);
                    }
                }
            }
        }
    }
    

     public void setJavaType(Type type) {
	 javaType = type;
         ensureTypeSortConformance();
     }
    
    public void setSort(Sort s) {
 	sort = s;
        ensureTypeSortConformance();
    }

    public Type getJavaType() {
	return javaType;
    }

    public Sort getSort() {
	return sort;
    }

    /** 
     * returns the default value of the given type 
     * according to JLS ???4.5.5 
     * @return the default value of the given type 
     * according to JLS ???4.5.5
     */
    public Literal getDefaultValue() {
	return javaType.getDefaultValue();
    }
    
    public String toString() {
	if (javaType == null) return "KeYJavaType:null,"+sort;
	return "(type, sort): ("+javaType.getName()+","+sort+")"; 
    }

    public String getFullName() {
	return getJavaType().getFullName();
    }

    public String getName() {
	return getJavaType().getName();
    }

    public PackageReference createPackagePrefix() {
	PackageReference ref = null;
	String rest = getFullName();
	if (rest.indexOf(".")>0) {
	    rest = rest.substring(0, rest.lastIndexOf(".")+1);
	    while (rest.indexOf(".")>0) {
		String name = rest.substring(0, rest.indexOf("."));
		rest = rest.substring(rest.indexOf(".")+1);
		ref = new PackageReference(new ProgramElementName(name), ref);
	    }
	}
	return ref;
    }

    public static final class LexicographicalKeYJavaTypeOrder implements Comparator {
        public int compare(Object arg0, Object arg1) {
            assert arg0 instanceof KeYJavaType && arg1 instanceof KeYJavaType;
            return ((KeYJavaType)arg0).getFullName().
                compareTo(((KeYJavaType)arg1).getFullName());
        }
    }
}

