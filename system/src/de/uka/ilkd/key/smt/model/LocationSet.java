package de.uka.ilkd.key.smt.model;

import java.util.LinkedList;
import java.util.List;

/**
 * A LocationSet represents a location set in an SMT model.
 * @author mihai
 *
 */

public class LocationSet {
	/**
	 * The name of the location set.
	 */
	private String name;
	/**
	 * The locations contained in the location set.
	 */
	private List<Location> locations;

	public LocationSet(String name) {
		this.name = name;
		locations = new LinkedList<Location>();
	}

	public String getName() {
		return name;
	}
	
	public void setName(String name){
		this.name = name;
	}
	
	public int size(){
		return locations.size();
	}
	
	

	public List<Location> getLocations() {
		return locations;
	}

	public void setLocations(List<Location> locations) {
		this.locations = locations;
	}

	public boolean add(Location e) {
		return locations.add(e);
	}

	public Location get(int index) {
		return locations.get(index);
	}

	public String toString() {

		String result = name;
		
		result += " = {";
		
		for(Location ls : locations){
			result+= ls;
			result+= ", ";
		}
		
		result = result.trim();
		if(result.contains(",")){
			result = result.substring(0,result.lastIndexOf(','));
		}
		result += "}";	


		return result;
	}
	/**
	 * Location sets with equal names are equal.
	 */
	public boolean equals(Object o){
		
		if(o instanceof LocationSet){
			
			LocationSet ls = (LocationSet) o;
			return ls.name.equals(name);
			
			
		}
		
		return false;
		
		
	}









}
