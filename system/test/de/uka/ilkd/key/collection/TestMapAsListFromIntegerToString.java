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

package de.uka.ilkd.key.collection;

import de.uka.ilkd.key.collection.DefaultImmutableMap;
import de.uka.ilkd.key.collection.ImmutableMap;

/** JUnit test for MapAsList<Integer,String> implementation */


public class TestMapAsListFromIntegerToString extends junit.framework.TestCase {

    private String[] entryStr;
    private Integer[] entryInt;

    /** puts i and str in the corresponding arrays at place nr */
    private void put(int nr,int i,String str) {
	entryInt[nr]=Integer.valueOf(i);
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

    private ImmutableMap<Integer,String> createMap() {
	ImmutableMap<Integer,String> map = DefaultImmutableMap.<Integer,String>nilMap();
	// create map with entrys like (1,"Eins")
	for (int i=0;i<entryStr.length;i++) {
	    map=map.put(entryInt[i],entryStr[i]);
	}
	return map;
    }

    public void testMapEntriesAreTheSameThatHaveBeenPutInside() {
	ImmutableMap<Integer,String> map=createMap();
	// assert that all entries are in list
	for (int i=0;i<entryStr.length;i++) {
	    assertEquals("Map does not contain entry("+entryInt[i]+
			", "+entryStr[i]+")",
			entryStr[i], map.get(entryInt[i]));
	}
    }

    public void testReplaceIfSameKeyWithNewValueIsPutInMap() {
	ImmutableMap<Integer,String> map=createMap();
	map=map.put(Integer.valueOf(0),"Zero");
	// zero is in list
	assertTrue("Zero is not in list.",map.containsValue("Zero"));
	// but not so old element Null with same key (0)
	assertTrue("Null is in list but should have been replaced by Zero",!map.containsValue("Null"));
    }

    public void testImmutability() {
	ImmutableMap<Integer,String> map=createMap();
	ImmutableMap<Integer,String> old=map;
	map=map.put(Integer.valueOf(5),"Fuenf");
	// 5 is in map but not in old
	assertTrue("Fuenf is not in map",map.containsValue("Fuenf"));
	assertTrue("Fuenf is in old map, but it should not be there. Map is not immutable.", !old.containsValue("Fuenf"));
    }

    public void testMapCanContainSameValueWithDifferentKeys() {
	ImmutableMap<Integer,String> map=createMap();
	// add a mapping with a value that has been mapped to
	// another key before
	Integer hundred=Integer.valueOf(100);
	map=map.put(hundred,entryStr[1]);
	assertSame(entryStr[1]+" is not mapped to the newer key 100", map.get(hundred),entryStr[1]);
	assertSame(entryStr[1]+" is not mapped to the older key "+entryInt[1], map.get(entryInt[1]),entryStr[1]);
    }

    public void testRemoveOneMappingWithSpecifiedKey() {
	ImmutableMap<Integer,String> map=createMap();
	// delete map (1,"Eins")
	map=map.remove(entryInt[1]);
	assertTrue("Deleted Mapping found in map", !map.containsKey(entryInt[1]));
    }

    public void testRemoveAllMappingToSpecifiedValue() {
	ImmutableMap<Integer,String> map=createMap();
	// add a mapping with a value that has been mapped to
	// another key before
	Integer hundred=Integer.valueOf(100);
	map=map.put(hundred,entryStr[1]);	
	// delete map (*,"Eins")
	map=map.removeAll(entryStr[1]);
	assertTrue("Value :"+entryStr[1]+" found in map. But I deleted all"+
		   " of these values :-(", !map.containsValue(entryStr[1]));
    }

    public void testSpecialCases() {
	ImmutableMap<Integer,String> map=DefaultImmutableMap.<Integer,String>nilMap();
	map = map.put(Integer.valueOf(0), "A");
	assertTrue("Map should be empty and therefore equal to the EMPTY_MAP",
	       map.remove(Integer.valueOf(0)).isEmpty());

	assertTrue("Repeated key removal should not change anything",
		   map.remove(Integer.valueOf(0)).remove(Integer.valueOf(0)).isEmpty());


	map = map.put(Integer.valueOf(0), "B");
	assertTrue("Map should have only one element with key 0 and value \"B\" ", 
	       map.size() == 1 && "B".equals(map.get(Integer.valueOf(0))));


	map = map.removeAll("B");
	assertTrue("Map should be empty",
		   map.isEmpty());


	map = map.put(Integer.valueOf(0), "B");
	map = map.put(Integer.valueOf(1), "C");
	map = map.put(Integer.valueOf(2), "B");
	
	map = map.removeAll("B");
	assertTrue("Map should not contain value \"B\" any longer ",
	       map.size() == 1 && !map.containsValue("B"));

	map = map.removeAll("B");
	assertTrue("Removing non-existant values should not change anything",
	       map.size() == 1 && !map.containsValue("B"));

    }


}