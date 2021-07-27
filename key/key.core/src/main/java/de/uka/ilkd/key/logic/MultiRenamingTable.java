// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.SourceElement;



public class MultiRenamingTable extends RenamingTable{

    private final HashMap<? extends SourceElement, ? extends SourceElement> hmap;

    public MultiRenamingTable(HashMap<? extends SourceElement, ? extends SourceElement> hmap){
	this.hmap = hmap;
    }

    public SourceElement  getRenaming(SourceElement se){
	return hmap.get(se);
    }

    public Iterator<? extends SourceElement> getRenamingIterator(){
	return hmap.keySet().iterator();
    }
    
    public String toString(){
	return ("MultiRenamingTable: "+hmap);
    }
    
    public HashMap<? extends SourceElement, ? extends SourceElement> getHashMap(){
        return hmap;
    }
    
}