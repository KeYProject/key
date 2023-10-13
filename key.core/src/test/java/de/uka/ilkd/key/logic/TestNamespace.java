/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;


/**
 * class tests the namespace
 */


public class TestNamespace {

    Namespace<LogicVariable> ns1;
    Namespace<LogicVariable> ns2;
    Namespace<LogicVariable> ns3;

    Sort s1;
    LogicVariable va;
    LogicVariable vb;
    LogicVariable vc;
    LogicVariable vd;
    LogicVariable ve;

    @BeforeEach
    public void setUp() {
        this.s1 = new SortImpl(new Name("S1"));
        this.va = new LogicVariable(new Name("A"), s1);
        this.vb = new LogicVariable(new Name("B"), s1);
        this.vc = new LogicVariable(new Name("C"), s1);
        this.vd = new LogicVariable(new Name("D"), s1);
        this.ve = new LogicVariable(new Name("E"), s1);

        ns1 = new Namespace<>();
        ns1.add(va);
        ns1.add(vb);
        ns2 = ns1.extended(vc);
        ns3 = ns2.extended(vd);
        ns3.add(ve);
    }

    @AfterEach
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

    @Test
    public void testNamespace1() {
        assertEquals(va, ns1.lookup(new Name("A")));
        assertEquals(vb, ns1.lookup(new Name("B")));
    }

    @Test
    public void testNamespace2() {
        assertEquals(va, ns2.lookup(new Name("A")));
        assertEquals(vb, ns2.lookup(new Name("B")));
        assertEquals(vc, ns2.lookup(new Name("C")));
        assertNull(ns2.lookup(new Name("D")));
    }

    @Test
    public void testNamespace3() {
        assertEquals(va, ns3.lookup(new Name("A")));
        assertEquals(vb, ns3.lookup(new Name("B")));
        assertEquals(vc, ns3.lookup(new Name("C")));
        assertEquals(vd, ns3.lookup(new Name("D")));
        assertEquals(ve, ns3.lookup(new Name("E")));
        assertNull(ns3.lookup(new Name("F")));
    }

    @Test
    public void testEmpty() {
        assertNull(new Namespace<LogicVariable>().lookup(new Name("A")));
    }

}
