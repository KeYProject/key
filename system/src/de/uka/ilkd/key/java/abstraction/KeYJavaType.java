// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Sort sort) {
	this.sort = sort;
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Type type) {
	this.javaType = type;
    }
    
    public void setJavaType(Type type) {
	javaType = type;
    }
    
    public void setSort(Sort s) {
 	sort = s;
    }

    public Type getJavaType() {
	return javaType;
    }

    public Sort getSort() {
	return sort;
    }

    /** 
     * returns the default value of the given type 
     * according to JLS Sect. 4.5.5 
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
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
    
    public boolean equals (Object o){
        try {
            return javaType.equals(((KeYJavaType)o).javaType) && sort.equals(((KeYJavaType)o).sort);
        } catch (Exception e) {
        return false;
        }
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

    public static final class LexicographicalKeYJavaTypeOrder<T extends KeYJavaType> 
    implements Comparator<T> {
        public int compare(T arg0, T arg1) {
            return arg0.getFullName().compareTo(arg1.getFullName());
        }
    }
}

