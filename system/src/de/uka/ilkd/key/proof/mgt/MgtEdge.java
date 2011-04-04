// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.*;

public class MgtEdge {

    Object from;
    Object to;
    Map<String,String> attrs = new HashMap();
    
    public MgtEdge(Object f, Object t, String ... attrString) {
        from = f;
	to = t;
	for(String s: attrString) {
	    if ("".equals(s)) continue;
	    String[] eq = s.split("=");
	    attrs.put(eq[0],eq[1]);
	}
    }
    
    public Object from() {
        return from;
    }
    
    public Object to() {
        return to;
    }
    
    public String printAttrs() {
        if (attrs.size()==0) return "";
	String s =" [";
	for (String key: attrs.keySet()) {
	    s=s+key+"="+attrs.get(key)+",";
	}
	return s.substring(0,s.length()-1)+"]";
    }
}
