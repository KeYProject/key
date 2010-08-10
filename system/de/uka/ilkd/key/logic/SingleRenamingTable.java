// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.LocationVariable;



public class SingleRenamingTable extends RenamingTable{

    SourceElement oldVar,newVar;
    LinkedList ll= new LinkedList();

    public SingleRenamingTable(SourceElement oldVar, SourceElement newVar){
	this.oldVar = oldVar;
	this.newVar = newVar;
	ll.add(oldVar);
    }

    public SourceElement  getRenaming(SourceElement se){
	if (se.equals(oldVar)) return newVar;
	return null;
    }

    public Iterator getRenamingIterator(){
	return ll.listIterator(0);
    }
    
    public String toString(){
        LocationVariable ov = (LocationVariable) oldVar;
        LocationVariable nv = (LocationVariable) newVar;
	return ("SingleRenamingTable: "+oldVar+" id: "+ ov.id() +" -> "+newVar + " id: " + nv.id());
    }
    
    public HashMap getHashMap(){
        HashMap hm = new HashMap();
        hm.put(oldVar,newVar);
        return hm;
    }

}
