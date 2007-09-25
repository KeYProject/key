// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import de.uka.ilkd.asmkey.util.TestUtil;
import de.uka.ilkd.asmkey.util.TestUtil.Item;
import de.uka.ilkd.asmkey.util.graph.CycleException;
import de.uka.ilkd.asmkey.util.graph.GraphException;
import de.uka.ilkd.key.logic.Name;

/**
 * the test class
 */
public class TestUnit extends TestUtil {

    public TestUnit() {
	
    }

    private Unit u1, u2, u3, u4, u5, u6;
    private UnitGraph graph;
    private Item i1, i2, i3, i4 ,i5 ,i6, i7, i8, i9, i10, i11;
    private Item s1, s2, s3, s4, s5, s6, s7, s8, s9,s10;

    public void setUp() throws GraphException, Exception {
	// creating the graphs and the units
	graph = new UnitGraph();
	u1 = new Unit("U1");
	u2 = new Unit("U2");
	u3 = new Unit("U3");
	u4 = new Unit("U4");
	u5 = new Unit("U5");
	u6 = new Unit("U6");

	graph.add(u1);
	graph.add(u2);
	graph.add(u3);
	graph.add(u4);
	graph.add(u5);
	graph.add(u6);
	
	graph.addEdge(u1,u3);
	graph.addEdge(u2,u3);
	graph.addEdge(u3,u4);
	graph.addEdge(u3,u5);
	graph.addEdge(u4,u6);
	graph.addEdge(u5,u6);

	//populating units namespaces
	i1 = addItem("U1.f", u1);
	i2 = addItem("U1.g", u1);
	i3 = addItem("U2.f", u2);
	i4 = addItem("U3.e", u3);
	i5 = addItem("U3.h", u3);
	i6 = addItem("U3.i", u3);
	i7 = addItem("U4.h", u4);
	i8 = addItem("U4.m", u4);
	i9 = addItem("U5.l", u5);
	i10 = addItem("U6.j", u6);
	i11 = addItem("U6.k", u6);

	//populates sorts
	s1 = addSort("U1.int", u1);
	s2 = addSort("[U1.int]", u1);
	addSort("U2.bin", u2);
	addSort("[U2.bin]", u2);
	s3 = addSort("U3.num", u3);
	s4 = addSort("[U3.num]", u3);
	s5 = addSort("U5.digit", u5);
	s6 = addSort("[U5.digit]", u5);
	s7 = addSort("U6.hex", u6);
	s8 = addSort("[U6.hex]", u6);
	s9 = addSort("U6.oct", u6);
	s10 = addSort("[U6.oct]", u6);
	
	ImportInfo[] imports = new ImportInfo[4];
	imports[0] = ImportInfo.createAllSymbolsImportInfo(u3);
	imports[1] = ImportInfo.createAllSymbolsImportInfo(u4);
	imports[2] = ImportInfo.createNoSymbolsImportInfo(u5);
        imports[3] = ImportInfo.createSomeSymbolsImportInfo
	    (u6, new RestrictedSymbol[] {
		new RestrictedSymbol(RestrictedSymbol.FUNCTION, "k"),
		new RestrictedSymbol(RestrictedSymbol.SORT, "hex") });
	u1.setImportInfos(imports);
	
    }

    private Item addItem(String symbol, Unit unit) throws Exception {
	Item item = new Item(symbol);
	unit.funcNS().add(item);
	return item;
    }

    private Item addSort(String symbol, Unit unit) throws Exception {
	Item item = new Item(symbol);
	unit.sortNS().add(item);
	return item;
    }

    private boolean testCyclicity(Unit start, Unit end) {
	try {
	    graph.addEdge(start,end);
	}
	catch(CycleException e) {
	    return true;
	}
	catch(Exception e) {
	    
	}
	return false;
    }

    private void testLookup(UnitNamespace ns, LookupUnit[] units) {
	for(int i=0; i<units.length; i++) {
	    assertEquals(units[i].message, units[i].item, ns.lookup(units[i].name));
	}
    }
    
    private void assertContainsUnit(Unit u) throws Exception {
	assertTrue("The graph should contain unit " + u, graph.contains(u));
    }
    
    private void assertContainsUnit(String u) throws Exception {
	assertTrue("The graph should contain unit " + u, graph.contains(new Name(u)));
    }

    private void unitRetrievalTest() throws Exception {
	assertContainsUnit(u1);
	assertContainsUnit(u2);
	assertContainsUnit(u3);
	assertContainsUnit(u4);
	assertContainsUnit(u5);
	assertContainsUnit(u6);
	for(int i =1; i<7; i++) {
	    assertContainsUnit("U" + i);
	}
    }
    
    private void topologicalSortTest() {
	ListOfUnit units; 
	ListOfUnit rev_units;
	ListOfUnit temp;
	Unit unit;

	rev_units = UnitUtil.convertAndReverse(graph.orderedIterator());
	units = rev_units.reverse();

	assertEquals("The list has not the good number of units", 6, units.size());
	assertEquals("U6 should be the first unit:", u6, units.head());
	
	while (rev_units != SLListOfUnit.EMPTY_LIST) {
	    unit = rev_units.head();
	    rev_units = rev_units.tail();
	    temp = rev_units;
	    while(temp != SLListOfUnit.EMPTY_LIST) {
		assertFalse(graph.containsPath(temp.head(), unit));
		temp = temp.tail();
	    }
	}
    } 

    private void lookupFuncTest() {
	LookupUnit[] units = new LookupUnit [] {
	    /* first lookup some full qualified names */
	    new LookupUnit("U1.f", i1),
	    new LookupUnit("U2.f", null),
	    new LookupUnit("U3.h", i5),
	    new LookupUnit("U6.j", i10),
	    new LookupUnit("U5.b", null),
	    /* then some relative */
	    new LookupUnit("g", i2),
	    new LookupUnit("e", i4),
	    new LookupUnit("h", i7), /* and not i5 as, u4 is imported 'after' i3 */
	    new LookupUnit("l", null),
	    new LookupUnit("k", i11),
	    new LookupUnit("j", null)
	};

	testLookup(u1.funcNS(), units);
    }
    
    private void lookupSortTest() {
	LookupUnit[] units = new LookupUnit[] {
	    /* first lookup some fully qualified names*/
	    new LookupUnit("U1.int", s1),
	    new LookupUnit("[U1.int]", s2),
	    new LookupUnit("U2.bin", null),
	    new LookupUnit("[U2.bin]", null),
	    new LookupUnit("U3.num", s3),
	    new LookupUnit("[U3.num]", s4),
	    new LookupUnit("U5.digit", s5),
	    new LookupUnit("[U5.digit]", s6),
	    new LookupUnit("U6.hex", s7),
	    new LookupUnit("[U6.hex]", s8),
	    new LookupUnit("U6.arg", null),
	    new LookupUnit("[U6.arg]", null),
	/* then lookup relative */
	    new LookupUnit("int", s1),
	    new LookupUnit("[int]", s2),
	    new LookupUnit("bin", null),
	    new LookupUnit("[bin]", null),
	    new LookupUnit("num", s3),
	    new LookupUnit("[num]", s4),
	    new LookupUnit("digit", null),
	    new LookupUnit("[digit]", null),
	    new LookupUnit("hex", s7),
	    new LookupUnit("[hex]", s8),
	    new LookupUnit("oct", null),
	    new LookupUnit("[oct]", null)
	};
	
	testLookup(u1.sortNS(), units);
    }

    private void cyclicityTest() {
	assertTrue(testCyclicity(u6, u1));
	assertTrue(testCyclicity(u6, u2));
	assertTrue(testCyclicity(u5, u1));
	assertFalse(testCyclicity(u1, u6));
	assertFalse(testCyclicity(u2, u6));
	assertFalse(testCyclicity(u1, u2));
    }
    
    public void testUnit() throws Exception {
	unitRetrievalTest();
	topologicalSortTest();
	lookupFuncTest();
	lookupSortTest();
	cyclicityTest();
    }

} 



class LookupUnit {

    public final String name;
    public final Item item;
    public final String message;

    public LookupUnit(String name, Item item, String message) {
	this.name = name;
	this.item = item;
	this.message = message;
    }

    public LookupUnit(String name, Item item) {
	this(name, item, "lookup: " + name + ";");
    }
}
