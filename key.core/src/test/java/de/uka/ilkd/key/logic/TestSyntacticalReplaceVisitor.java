/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.JOperatorSV;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestSyntacticalReplaceVisitor {

    SVInstantiations insts = null;

    JTerm rw;
    JTerm t_allxpxpx;

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
        var u = (JOperatorSV) rw.varsBoundHere(0).get(0);

        SchemaVariable b = (SchemaVariable) rw.sub(0).sub(0).op();

        SchemaVariable c = (SchemaVariable) rw.sub(0).sub(1).sub(1).op();

        SchemaVariable v = (SchemaVariable) rw.sub(0).sub(1).varsBoundHere(1).get(0);

        Sort s = u.sort();

        LogicVariable x = new LogicVariable(new Name("x"), s);
        LogicVariable y = new LogicVariable(new Name("y"), s);
        Function p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, s);

        JTerm t_x = TB.tf().createTerm(x);
        JTerm t_px = TB.tf().createTerm(p, new JTerm[] { t_x }, null, null);
        JTerm t_y = TB.tf().createTerm(y);
        JTerm t_py = TB.tf().createTerm(p, new JTerm[] { t_y }, null, null);

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
            null, insts, TacletForTests.createGoal(), null, null);
        rw.execPostOrder(srv);
        assertEquals(srv.getTerm(), t_allxpxpx);
    }


    @Test
    public void testSubstitutionReplacement() {
        JTerm orig = TacletForTests.parseTerm("{\\subst s x; f(const)}(\\forall s y; p(x))");
        JTerm result = TacletForTests.parseTerm("(\\forall s y; p(f(const)))");
        var goal = TacletForTests.createGoal();
        SyntacticalReplaceVisitor v = new SyntacticalReplaceVisitor(new TermLabelState(), null,
            null, SVInstantiations.EMPTY_SVINSTANTIATIONS, goal, null, null);
        orig.execPostOrder(v);
        assertEquals(v.getTerm().sub(0), result.sub(0),
            "Substitution Term not resolved correctly.");
    }
}
