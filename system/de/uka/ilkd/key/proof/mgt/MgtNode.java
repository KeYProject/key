// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.*;

public class MgtNode {

    Object content;
    
    Set<MgtEdge> in  = new HashSet();
    Set<MgtEdge> out = new HashSet();

    Map<String,String> attrs = new HashMap();

    public MgtNode(Object  o, String ... attrString) {
        content = o;
        addAttr(attrString);
    }
    
    public void addAttr(String ... attrString) {
	for(String s: attrString) {
	    if ("".equals(s)) continue;
	    String[] eq = s.split("=");
	    String old = attrs.get(eq[0]);
	    if (old==null) {
	        attrs.put(eq[0],eq[1]);
            } else {
                //append new attr
                attrs.put(eq[0], old+","+eq[1]);
            }
	}
    }
    
    public void addInEdge(MgtEdge e) {
        in.add(e);
    }
    
    public void addOutEdge(MgtEdge e) {
        out.add(e);
    }
    
    public int inDegree() {
        return in.size();
    }
    
    public int outDegree() {
        return out.size();
    }
    
    public Set<MgtEdge> incoming() {
        return in;
    }
    
    public String printAttrs() {
        if (attrs.size()==0) return "";
	String s =" [";
	for (String key: attrs.keySet()) {
	    s=s+key+"=\""+attrs.get(key)+"\",";
	}
	return s.substring(0,s.length()-1)+"]";
    }
    
    public String getAttr(String key) {
        String a = attrs.get(key);
        return (a==null) ? "" : a;
    }
    
    public Object getContent() {
        return content;
    }
    
}
