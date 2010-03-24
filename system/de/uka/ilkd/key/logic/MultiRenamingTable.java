// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.SourceElement;



public class MultiRenamingTable extends RenamingTable{

    private final HashMap hmap;

    public MultiRenamingTable(HashMap hmap){
	this.hmap = hmap;
    }

    public SourceElement  getRenaming(SourceElement se){
	return (SourceElement) hmap.get(se);
    }

    public Iterator getRenamingIterator(){
	return hmap.keySet().iterator();
    }
    
    public String toString(){
	return ("MultiRenamingTable: "+hmap);
    }
    
    public HashMap getHashMap(){
        return hmap;
    }
    
}
