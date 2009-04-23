// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.collection;

/** JUnit test for MapAsListFromIntegerToString implementation */


public class TestMapAsListFromIntegerToString extends junit.framework.TestCase {

    private String[] entryStr;
    private Integer[] entryInt;

    /** puts i and str in the corresponding arrays at place nr */
    private void put(int nr,int i,String str) {
	entryInt[nr]=new Integer(i);
	entryStr[nr]=str;
    }

    public TestMapAsListFromIntegerToString(String name) {
	super(name);
    }

    public void setUp() {
	entryStr=new String[4];
	entryInt=new Integer[4];
	put(0,0,"Null");
	put(1,1,"Eins");
	put(2,2,"Zwei");
	put(3,3,"Drei");  
    }

    private MapFromIntegerToString createMap() {
	MapFromIntegerToString map=MapAsListFromIntegerToString.EMPTY_MAP;
	// create map with entrys like (1,"Eins")
	for (int i=0;i<entryStr.length;i++) {
	    map=map.put(entryInt[i],entryStr[i]);	    
	}
	return map;
    }
   
    public void testMapEntriesAreTheSameThatHaveBeenPutInside() {
	MapFromIntegerToString map=createMap();
	// assert that all entries are in list
	for (int i=0;i<entryStr.length;i++) {
	    assertEquals("Map does not contain entry("+entryInt[i]+
			", "+entryStr[i]+")",
			map.get(entryInt[i]),entryStr[i]); 
	}
    }

    public void testReplaceIfSameKeyWithNewValueIsPutInMap() {
	MapFromIntegerToString map=createMap();
	map=map.put(new Integer(0),"Zero");
	// zero is in list
	assertTrue("Zero is not in list.",map.containsValue("Zero"));
	// but not so old element Null with same key (0)
	assertTrue("Null is in list but should have been replaced by Zero",!map.containsValue("Null"));
    }

    public void testImmutability() {
	MapFromIntegerToString map=createMap();
	MapFromIntegerToString old=map;
	map=map.put(new Integer(5),"Fuenf");
	// 5 is in map but not in old
	assertTrue("Fuenf is not in map",map.containsValue("Fuenf"));
	assertTrue("Fuenf is in old map, but it should not be there. Map is not immutable.", !old.containsValue("Fuenf"));
    }

    public void testMapCanContainSameValueWithDifferentKeys() {
	MapFromIntegerToString map=createMap();
	// add a mapping with a value that has been mapped to 
	// another key before
	Integer hundred=new Integer(100);
	map=map.put(hundred,entryStr[1]);
	assertSame(entryStr[1]+" is not mapped to the newer key 100", map.get(hundred),entryStr[1]);
	assertSame(entryStr[1]+" is not mapped to the older key "+entryInt[1], map.get(entryInt[1]),entryStr[1]);   
    } 
    
    public void testRemoveOneMappingWithSpecifiedKey() {
	MapFromIntegerToString map=createMap();
	// delete map (1,"Eins")
	map=map.remove(entryInt[1]);
	assertTrue("Deleted Mapping found in map", !map.containsKey(entryInt[1]));
    }

    public void testRemoveAllMappingToSpecifiedValue() {
	MapFromIntegerToString map=createMap();
	// add a mapping with a value that has been mapped to 
	// another key before
	Integer hundred=new Integer(100);
	map=map.put(hundred,entryStr[1]);	
	// delete map (*,"Eins")
	map=map.removeAll(entryStr[1]);
	assertTrue("Value :"+entryStr[1]+" found in map. But I deleted all"+
		   " of these values :-(", !map.containsValue(entryStr[1])); 
    }

    public void testSpecialCases() {
	MapFromIntegerToString map=MapAsListFromIntegerToString.EMPTY_MAP;
	map = map.put(new Integer(0), "A");
	assertTrue("Map should be empty and therefore equal to the EMPTY_MAP", 
	       map.remove(new Integer(0)).isEmpty());
	
	assertTrue("Repeated key removal should not change anything", 
		   map.remove(new Integer(0)).remove(new Integer(0)).isEmpty());


	map = map.put(new Integer(0), "B");
	assertTrue("Map should have only one element with key 0 and value \"B\" ", 
	       map.size() == 1 && "B".equals(map.get(new Integer(0))));


	map = map.removeAll("B");
	assertTrue("Map should be empty", 
		   map.isEmpty());


	map = map.put(new Integer(0), "B");
	map = map.put(new Integer(1), "C");
	map = map.put(new Integer(2), "B");
	
	map = map.removeAll("B");
	assertTrue("Map should not contain value \"B\" any longer ", 
	       map.size() == 1 && !map.containsValue("B"));
	 
	map = map.removeAll("B");
	assertTrue("Removing non-existant values should not change anything", 
	       map.size() == 1 && !map.containsValue("B"));
	
    }

   
}
