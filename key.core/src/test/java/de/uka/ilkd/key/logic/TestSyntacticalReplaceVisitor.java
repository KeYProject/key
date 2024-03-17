/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestSyntacticalReplaceVisitor {

    SVInstantiations insts = null;

    Term rw;
    Term t_allxpxpx;

    @BeforeEach
    public void setUp() {
        TacletIndex index;
        TacletForTests.setStandardFile(TacletForTests.testRules);
        TacletForTests.parse();
        index = TacletForTests.getRules();
        TermBuilder TB = TacletForTests.services().getTermBuilder();

        RewriteTaclet taclet =
            (RewriteTaclet) index.lookup("testSyntacticalReplaceVisitor_0").taclet();
        rw = ((RewriteTacletGoalTemplate) taclet.goalTemplates().head()).replaceWith();
        SchemaVariable u = (SchemaVariable) rw.varsBoundHere(0).get(0);

        SchemaVariable b = (SchemaVariable) rw.sub(0).sub(0).op();

        SchemaVariable c = (SchemaVariable) rw.sub(0).sub(1).sub(1).op();

        SchemaVariable v = (SchemaVariable) rw.sub(0).sub(1).varsBoundHere(1).get(0);

        Sort s = u.sort();

        LogicVariable x = new LogicVariable(new Name("x"), s);
        LogicVariable y = new LogicVariable(new Name("y"), s);
        JFunction p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, s);

        Term t_x = TB.tf().createTerm(x);
        Term t_px = TB.tf().createTerm(p, new Term[] { t_x }, null, null);
        Term t_y = TB.tf().createTerm(y);
        Term t_py = TB.tf().createTerm(p, new Term[] { t_y }, null, null);

        Services services = TacletForTests.services();
        insts = SVInstantiations.EMPTY_SVINSTANTIATIONS.add(b, t_px, services).add(v, t_y, services)
                .add(u, t_x, services).add(c, t_py, services);

        t_allxpxpx = TB.all(x, TB.and(t_px, t_px));

    }

    @AfterEach
    public void tearDown() {
        insts = null;
        rw = null;
        t_allxpxpx = null;
    }

    @Test
    public void test1() {
        SyntacticalReplaceVisitor srv = new SyntacticalReplaceVisitor(new TermLabelState(), null,
            null, insts, null, null, null, TacletForTests.services());
        rw.execPostOrder(srv);
        assertEquals(srv.getTerm(), t_allxpxpx);
    }


    @Test
    public void testSubstitutionReplacement() {
        Term orig = TacletForTests.parseTerm("{\\subst s x; f(const)}(\\forall s y; p(x))");
        Term result = TacletForTests.parseTerm("(\\forall s y; p(f(const)))");
        SyntacticalReplaceVisitor v = new SyntacticalReplaceVisitor(new TermLabelState(), null,
            null, SVInstantiations.EMPTY_SVINSTANTIATIONS, null, null, null,
            TacletForTests.services());
        orig.execPostOrder(v);
        assertEquals(v.getTerm().sub(0), result.sub(0),
            "Substitution Term not resolved correctly.");
    }
}
