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
import java.util.Map.Entry;

import de.uka.ilkd.key.java.SourceElement;


public abstract class RenamingTable{

    public abstract SourceElement  getRenaming(SourceElement se);

    public abstract Iterator<? extends SourceElement> getRenamingIterator();

    public static RenamingTable getRenamingTable(HashMap<? extends SourceElement, ? extends SourceElement> hmap){
	if (hmap.size()==0)return null;
	if (hmap.size()==1){
	    Entry<? extends SourceElement, ? extends SourceElement> entry = 
	            hmap.entrySet().iterator().next();
	    return new SingleRenamingTable(entry.getKey(), entry.getValue());
	}
	else return new MultiRenamingTable(hmap);
    }
    
    public abstract HashMap<? extends SourceElement, ? extends SourceElement> getHashMap();

}
