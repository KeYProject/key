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
