// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.casetool;

import java.util.HashMap;
import java.util.Iterator;

/**
 * @deprecated
 */
public class HashMapOfClassifier extends HashMap {
    
    public HashMapOfClassifier() {
	super();
    }

    public void putClassifier(String name, 
			      UMLOCLClassifier classifier) {
	put(name, classifier);
    }


    public UMLOCLClassifier getClassifier(String name) {
	return (UMLOCLClassifier)get(name);
    }

    public UMLOCLClassifier getClassifierByFullName(String name) {
	Iterator it = this.values().iterator();
	UMLOCLClassifier cls;
	while (it.hasNext()) {
	    cls=(UMLOCLClassifier)it.next();
	    if (cls.getFullName().equals(name))
	    	return cls;
	}
	return null;
    }


    public String toString() {
	Iterator it = keySet().iterator();	
	StringBuffer result = new StringBuffer();
	result.append("\n--------------------------------\n");
	while (it.hasNext()) {	   
	    result.append("key: "+it.next()+"\n");
	}
	result.append("\n--------------------------------\n");
	return result.toString();
    }

}
