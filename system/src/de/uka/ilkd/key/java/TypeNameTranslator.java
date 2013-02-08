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


package de.uka.ilkd.key.java;

public class TypeNameTranslator{

    private TypeNameTranslator() {}


    /**
     * returns the basetype of <code>t</code>. 
     * example: <code>getBaseType("[[[I")</code> returns "int".
     */
    public static String getBaseType(String t){
	if(t==null || !t.startsWith("[")){
	    return t;
	}
	while(t.startsWith("[")){
	    t = t.substring(1);
	}
	if(t.startsWith("L")){
	    return t.substring(1);
	}else if(t.startsWith("B")){
	    return "byte";
	}else if(t.startsWith("C")){
	    return "char";
	}else if(t.startsWith("D")){
	    return "double";
	}else if(t.startsWith("F")){
	    return "float";
	}else if(t.startsWith("I")){
	    return "int";
	}else if(t.startsWith("J")){
	    return "long";
	}else if(t.startsWith("S")){
	    return "short";
	}else if(t.startsWith("Z")){
	    return "boolean";
	}else{
	    return t;
	}
    }
    

    /** returns the dimensions of an ArrayType. Returns 0 if 
     * <code>t</code> doesn't represent an ArrayType.
     */
    public static int getDimensions(String t){
	if(t==null || !t.startsWith("[")){
	    return 0;
	}
	int i=0;
	while(t.startsWith("[")){
	    t = t.substring(1);
	    i++;
	}
	return i;
    }
    
}
