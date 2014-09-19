package de.uka.ilkd.key.testgen.oracle;

import java.util.HashSet;
import java.util.Set;

public class OracleLocationSet {
	
	private Set<OracleLocation> locs;	
	
	public OracleLocationSet() {
		locs = new HashSet<OracleLocation>();
	}
	
	private void add(OracleLocation loc){	
		locs.add(loc);		
	}
	
	private void add(OracleLocationSet loc){	
		locs.addAll(loc.locs);		
	}
	
	public OracleLocationSet singleton(OracleLocation loc){
		OracleLocationSet result = new OracleLocationSet();
		result.add(loc);
		return result;
	}
	
	public OracleLocationSet union(OracleLocationSet l1, OracleLocationSet l2){
		OracleLocationSet result = new OracleLocationSet();
		result.add(l1);
		result.add(l2);
		return result;		
	}
	
	public OracleLocationSet intersect(OracleLocationSet l1, OracleLocationSet l2){
		
		OracleLocationSet result = new OracleLocationSet();
		for(OracleLocation l : l1.locs){
			if(l2.contains(l)){
				result.add(l);
			}
		}
		
		
		for(OracleLocation l : l2.locs){
			if(l1.contains(l)){
				result.add(l);
			}
		}
		
		return result;
	}
	
	public boolean contains(OracleLocation l){
		for(OracleLocation loc : locs){
			
			if(loc.equals(l)){
				return true;
			}
			
			if(loc.isAllFields() && loc.getObject().equals(l.getObject())){
				return true;
			}
			
		}
		
		return false;
	}
}
