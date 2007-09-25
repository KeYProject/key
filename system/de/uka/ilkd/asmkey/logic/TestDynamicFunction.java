// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic;

import junit.framework.TestCase;
import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;


/** class tests the dynamic functions.
 *@see de.uka.ilkd.key.logic.TestTerm
 *
 *@author Stanislas Nanchen
 */


public class TestDynamicFunction extends TestCase { 

    public TestDynamicFunction() {

    }

    private AsmTermFactory factory = AsmTermFactory.ASMDEFAULT;

    private PrimitiveSort prim;

    private NonRigidFunction f;
    private RigidFunction g;

    private Term x, y, z;

    private Term t1, t2, t3, t4, t5, t6;

    public void setUp() {
	prim = new PrimitiveSort(new Name("primSort"));
	f = new NonRigidFunction(new Name("f"), prim, new Sort[] {prim, prim});
	g = new RigidFunction(new Name("g"), prim, new Sort[] {prim, prim});
	x = factory.createFunctionTerm(new LogicVariable(new Name("x"), prim));
	y = factory.createFunctionTerm(new LogicVariable(new Name("y"), prim));
	z = factory.createFunctionTerm(new LogicVariable(new Name("z"), prim));

	t1 = factory.createFunctionTerm(f, x, y);
	t2 = factory.createFunctionTerm(g, x, y);
	t3 = factory.createFunctionTerm(f, z, t1);
	t4 = factory.createFunctionTerm(f, t2, z);
	t5 = factory.createFunctionTerm(g, t1, z);
	t6 = factory.createFunctionTerm(g, z, t2);
    }

    private void dynamicTest() {
	assertFalse("t1 should be dynamic (non-rigid).",
		    t1.isRigid());

	assertTrue("t2 should be static (rigid).",
		   t2.isRigid());

	assertFalse("t3 should be dynamic (non-rigid).",
		    t3.isRigid());

	assertFalse("t4 should be dynamic (non-rigid).",
		     t4.isRigid());

	assertFalse("t5 should be dynamic (non-rigid).",
		     t5.isRigid());

	assertTrue("t6 should be static (rigid).",
		    t6.isRigid());
    }

    private void staticArgsTest() {
	assertTrue("t1 should have static (rigid) args.",
		   t1.hasRigidSubterms());

	assertTrue("t2 should have static (rigid) args.",
		   t2.hasRigidSubterms());

	assertFalse("t3 should not have static (rigid) args.",
		    t3.hasRigidSubterms());

	assertTrue("t4 should have static (rigid) args.",
		   t4.hasRigidSubterms());

	assertFalse("t5 should not have static (rigid) args.",
		    t5.hasRigidSubterms());

	assertTrue("t6 should have static (rigid) args.",
		   t6.hasRigidSubterms());
	
    }

    public void testDynamicFunction() {
	dynamicTest();
	staticArgsTest();
    }

}
