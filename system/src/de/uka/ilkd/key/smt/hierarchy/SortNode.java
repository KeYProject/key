package de.uka.ilkd.key.smt.hierarchy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a node in the class hierarchy. Each SortNode contains a Sort and links to SortNodes
 * containing the parents and the children of the sort.
 * @author mihai
 *
 */

public class SortNode {
    
    private Sort sort;
    
    private Set<SortNode> parents;
    private Set<SortNode> children;
    
    public SortNode(Sort sort){
	this.sort = sort;
	parents = new HashSet<SortNode>();
	children = new HashSet<SortNode>();
    }
    
    public void removeParent(SortNode s){
	parents.remove(s);
    }
    
    public void addParent(SortNode s){
	parents.add(s);
    }
    
    public void removeChild(SortNode s){
	children.remove(s);
    }
    
    public void addChild(SortNode s){
	children.add(s);
    }


    public Sort getSort() {
        return sort;
    }


    public Set<SortNode> getParents() {
        return parents;
    }


    public Set<SortNode> getChildren() {
        return children;
    }
    
    public String toString(){
	return sort.toString();
    }
    
    public boolean equals(Object o){
	if(this == o){
	    return true;
	}
	if(o instanceof SortNode){
	    Sort s = ((SortNode) o).getSort();
	    boolean result = s.toString().equals(sort.toString());
	    if(result){
		System.err.println(s+"=="+sort);
	    }
	}
	
	return false;
	
    }
    
    
    
    

}
