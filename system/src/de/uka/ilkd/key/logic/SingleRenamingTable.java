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
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.LocationVariable;



public class SingleRenamingTable extends RenamingTable{

    SourceElement oldVar,newVar;

    public SingleRenamingTable(SourceElement oldVar, SourceElement newVar){
	this.oldVar = oldVar;
	this.newVar = newVar;
    }

    public SourceElement  getRenaming(SourceElement se){
	if (se.equals(oldVar)) return newVar;
	return null;
    }

    public Iterator<SourceElement> getRenamingIterator(){
	return new SingleIterator(oldVar);
    }
    
    public String toString(){
        LocationVariable ov = (LocationVariable) oldVar;
        LocationVariable nv = (LocationVariable) newVar;
	return ("SingleRenamingTable: "+oldVar+" id: "+ System.identityHashCode(ov) +" -> "+
	                newVar + " id: " + System.identityHashCode(nv));
    }
    
    public HashMap<SourceElement, SourceElement> getHashMap(){
        HashMap<SourceElement, SourceElement> hm = new LinkedHashMap<SourceElement, SourceElement>();
        hm.put(oldVar,newVar);
        return hm;
    }

    private static class SingleIterator implements Iterator<SourceElement> {

        private SourceElement se;

        public SingleIterator(SourceElement se) {
            this.se = se;           
        }

        @Override
        public boolean hasNext() {
            return se != null;
        }

        @Override
        public SourceElement next() {
            final SourceElement next = se;
            se = null;
            return next;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
   }
    
}
