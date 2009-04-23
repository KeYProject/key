// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TestSyntacticalReplaceVisitor extends TestCase {
    
    
    SVInstantiations insts=null;

    Term rw;
    Term t_allxpxpx;
    private final static TermFactory tf=TermFactory.DEFAULT;

    public TestSyntacticalReplaceVisitor(String s) {
	super(s);
    }

    public void setUp() {
	TacletIndex index=null;
	TacletForTests.setStandardFile(TacletForTests.testRules);
	TacletForTests.parse();
	index=TacletForTests.getRules();
	RewriteTaclet taclet
	    = (RewriteTaclet)index.lookup("testSyntacticalReplaceVisitor_0")
	    .taclet();
	rw=((RewriteTacletGoalTemplate)taclet.goalTemplates().head())
	    .replaceWith();
	SchemaVariable u=(SchemaVariable)rw.varsBoundHere(0)
	    .getQuantifiableVariable(0);

	SchemaVariable b=(SchemaVariable)rw.sub(0).sub(0).op();

	SchemaVariable c=(SchemaVariable)rw.sub(0).sub(1).sub(1).op();

	SchemaVariable v=(SchemaVariable)rw.sub(0).sub(1)
	    .varsBoundHere(1).getQuantifiableVariable(0);

	Sort s=((SortedSchemaVariable)u).sort();

	LogicVariable x=new LogicVariable(new Name("x"), s);
	LogicVariable y=new LogicVariable(new Name("y"), s);
	Function p=new RigidFunction(new Name("p"), Sort.FORMULA, new Sort[]{s});

	Term t_x=tf.createVariableTerm(x);
	Term t_px=tf.createFunctionTerm(p, t_x);
	Term t_y=tf.createVariableTerm(y);
	Term t_py=tf.createFunctionTerm(p, t_y);

	insts=SVInstantiations.EMPTY_SVINSTANTIATIONS.add(b, t_px).add(v, t_y)
	    .add(u, t_x).add(c, t_py);
	
	t_allxpxpx=tf.createQuantifierTerm(Op.ALL, x, tf.createJunctorTerm
					   (Op.AND, t_px, t_px));

    }
    
    public void tearDown() {
        insts = null;
        rw = null;
        t_allxpxpx = null;
    }

    public void test1() {
	SyntacticalReplaceVisitor srv=new SyntacticalReplaceVisitor(null, insts);
	rw.execPostOrder(srv);
	assertEquals(srv.getTerm(), t_allxpxpx);
    }
   

    public void testSubstitutionReplacement() {
	Term orig=TacletForTests.parseTerm("{\\subst s x; f(const)}(\\forall s y; p(x))");
	Term result=TacletForTests.parseTerm("(\\forall s y; p(f(const)))");
	SyntacticalReplaceVisitor v = new
	    SyntacticalReplaceVisitor
	    (null, SVInstantiations.EMPTY_SVINSTANTIATIONS);
	orig.execPostOrder(v);
	assertEquals("Substitution Term not resolved correctly.",
		     v.getTerm().sub(0), result.sub(0));
    }
}
