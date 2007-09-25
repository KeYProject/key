package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.SourceElement;


public abstract class RenamingTable{

    public abstract SourceElement  getRenaming(SourceElement se);

    public abstract Iterator getRenamingIterator();

    public static RenamingTable getRenamingTable(HashMap hmap){
	if (hmap.size()==0)return null;
	if (hmap.size()==1){
	    Object[] oldVar= hmap.keySet().toArray();
	    Object newVar= hmap.get(oldVar[0]);
	    return new SingleRenamingTable((SourceElement)oldVar[0],(SourceElement)newVar);
	}
	else return new MultiRenamingTable(hmap);
    }
    
    public abstract HashMap getHashMap();

}
