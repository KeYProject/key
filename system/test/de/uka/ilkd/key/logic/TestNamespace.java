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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import junit.framework.TestCase;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.logic.sort.Sort;


/** class tests the namespace
*/


public class TestNamespace extends TestCase {
    
    Namespace ns1;
    Namespace ns2;
    Namespace ns3;
    
    Sort s1;
    LogicVariable va;
    LogicVariable vb;
    LogicVariable vc;
    LogicVariable vd;
    LogicVariable ve;

    public TestNamespace(String name) {
	super(name);
    }

    public void setUp() {
        this.s1 = new SortImpl(new Name("S1"));
        this.va = new LogicVariable(new Name("A"),s1);
        this.vb = new LogicVariable(new Name("B"),s1);
        this.vc = new LogicVariable(new Name("C"),s1);
        this.vd = new LogicVariable(new Name("D"),s1);
        this.ve = new LogicVariable(new Name("E"),s1);
        
	ns1=new Namespace();
	ns1.add(va);
	ns1.add(vb);
	ns2=ns1.extended(vc);
	ns3=ns2.extended(vd);
	ns3.add(ve);
    }
    
    public void tearDown() {
        ns1 = null;
        ns2 = null;
        ns3 = null;        

        this.s1 = null;
        this.va = null;
        this.vb = null;
        this.vc = null;
        this.vd = null;
        this.ve = null;
    }

    public void testNamespace1() {
	assertEquals(va,ns1.lookup(new Name("A")));
	assertEquals(vb,ns1.lookup(new Name("B")));
    }

    public void testNamespace2() {
	assertEquals(va,ns2.lookup(new Name("A")));
	assertEquals(vb,ns2.lookup(new Name("B")));
	assertEquals(vc,ns2.lookup(new Name("C")));
	assertNull(ns2.lookup(new Name("D")));
    }

    public void testNamespace3() {
	assertEquals(va,ns3.lookup(new Name("A")));
	assertEquals(vb,ns3.lookup(new Name("B")));
	assertEquals(vc,ns3.lookup(new Name("C")));
	assertEquals(vd,ns3.lookup(new Name("D")));
	assertEquals(ve,ns3.lookup(new Name("E")));
	assertNull(ns3.lookup(new Name("F")));
    }

    public void testEmpty() {
	assertNull(new Namespace().lookup(new Name("A")));
    }

}