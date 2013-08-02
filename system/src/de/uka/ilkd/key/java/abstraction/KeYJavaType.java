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

package de.uka.ilkd.key.java.abstraction;

import java.util.Comparator;

import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The KeY java type realises a tuple (sort, type) of a logic sort and
 * the java type (for example a class declaration). 
 * In contrast to other classes the KeYJavaType is <emph>not</emph>
 * immutable, so use it with care. 
 */
public class KeYJavaType implements Type {

    /** Special return "type" for void methods. */
    public static final KeYJavaType VOID_TYPE = new KeYJavaType(null,Sort.ANY);

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
     * Returns the default value of the given type 
     * according to JLS Sect. 4.5.5;
     * returns null if this is not a real Java type. 
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
     */
    public Literal getDefaultValue() {
        if (javaType == null) return null;
        return javaType.getDefaultValue();
    }
    
    public String toString() {
        if (this == VOID_TYPE)
            return "KeYJavaType:void";
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
            return MiscTools.equalsOrNull(javaType,((KeYJavaType)o).javaType) && 
                    MiscTools.equalsOrNull(sort,((KeYJavaType)o).sort);
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

