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


package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.LocationVariable;



public class SingleRenamingTable extends RenamingTable{

    SourceElement oldVar,newVar;
    LinkedList<SourceElement> ll= new LinkedList<SourceElement>();

    public SingleRenamingTable(SourceElement oldVar, SourceElement newVar){
	this.oldVar = oldVar;
	this.newVar = newVar;
	ll.add(oldVar);
    }

    public SourceElement  getRenaming(SourceElement se){
	if (se.equals(oldVar)) return newVar;
	return null;
    }

    public Iterator<SourceElement> getRenamingIterator(){
	return ll.listIterator(0);
    }
    
    public String toString(){
        LocationVariable ov = (LocationVariable) oldVar;
        LocationVariable nv = (LocationVariable) newVar;
	return ("SingleRenamingTable: "+oldVar+" id: "+ ov.id() +" -> "+newVar + " id: " + nv.id());
    }
    
    public HashMap<SourceElement, SourceElement> getHashMap(){
        HashMap<SourceElement, SourceElement> hm = new HashMap<SourceElement, SourceElement>();
        hm.put(oldVar,newVar);
        return hm;
    }

}
