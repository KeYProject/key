/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.JavaDLFunction;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;


// most Code are copyed from Logic.TestUpdateFactory

public class TestTriggersSet {

    private Proof proof;

    private final Namespace<QuantifiableVariable> variables = new Namespace<>();

    private final Namespace<JavaDLFunction> functions = new Namespace<>();

    private final Namespace<Sort> sorts = new Namespace<>();

    // sort
    private Sort r;
    private Sort s;
    private Sort t;
    // private Sort ints ;


    // constant function
    private JavaDLFunction r_a;
    private JavaDLFunction r_b;
    private JavaDLFunction r_c;

    private JavaDLFunction s_a;
    private JavaDLFunction s_b;
    private JavaDLFunction s_c;

    private JavaDLFunction t_a;
    private JavaDLFunction t_b;
    private JavaDLFunction t_c;

    // Rigid function
    private JavaDLFunction frr; // r->r
    private JavaDLFunction f2rr; // r->r
    private JavaDLFunction fsr; // s-> r
    private JavaDLFunction ftr; // t->r
    private JavaDLFunction fstr;// s->t->r
    private JavaDLFunction frstr;// r->s->t->r;

    private JavaDLFunction gss; // s->s
    private JavaDLFunction grs; // r->s
    private JavaDLFunction gts; // t->s
    private JavaDLFunction grts; // r->t->s
    private JavaDLFunction grsts;// r->s->t->s

    private JavaDLFunction htt; // t->t
    private JavaDLFunction hrt; // r -> t
    private JavaDLFunction hst; // s->t
    private JavaDLFunction hrst;// r->s->t
    private JavaDLFunction hrstt;// t->s->t->t

    // Formular function
    private JavaDLFunction pp;// Formula->Formula
    private JavaDLFunction pr;// r->Formula
    private JavaDLFunction ps;// s->Formula
    private JavaDLFunction pt;// t->Formula
    private JavaDLFunction prs;// r->s->Formula
    private JavaDLFunction pst;// s->t->Formula
    private JavaDLFunction prt;// r->t->Formula
    private JavaDLFunction prst;// r->s->t->Formula
    // private Function pi;//ints->Formula
    private Goal g;

    public TestTriggersSet() {
        super();
    }

    @BeforeEach
    public void setUp() {
        // sort
        r = new SortImpl(new Name("r"));
        s = new SortImpl(new Name("s"));
        t = new SortImpl(new Name("t"));
        // ints =
        // ProofSettings.DEFAULT_SETTINGS.getLDTSettings().getIntegerSemantics().getIntSort();
        sorts.add(r);
        sorts.add(s);
        sorts.add(t);
        // sorts.add(ints);

        // constant
        r_a = new JavaDLFunction(new Name("r_a"), r, new Sort[0]);
        r_b = new JavaDLFunction(new Name("r_b"), r, new Sort[0]);
        r_c = new JavaDLFunction(new Name("r_c"), r, new Sort[0]);
        functions.add(r_a);
        functions.add(r_b);
        functions.add(r_c);

        s_a = new JavaDLFunction(new Name("s_a"), s, new Sort[0]);
        s_b = new JavaDLFunction(new Name("s_b"), s, new Sort[0]);
        s_c = new JavaDLFunction(new Name("s_c"), s, new Sort[0]);
        functions.add(s_a);
        functions.add(s_b);
        functions.add(s_c);

        t_a = new JavaDLFunction(new Name("t_a"), s, new Sort[0]);
        t_b = new JavaDLFunction(new Name("t_b"), s, new Sort[0]);
        t_c = new JavaDLFunction(new Name("t_c"), s, new Sort[0]);
        functions.add(t_a);
        functions.add(t_b);
        functions.add(t_c);


        // function
        frr = new JavaDLFunction(new Name("frr"), r, r);
        f2rr = new JavaDLFunction(new Name("f2rr"), r, r);
        fsr = new JavaDLFunction(new Name("fsr"), r, s);
        ftr = new JavaDLFunction(new Name("ftr"), r, t);
        fstr = new JavaDLFunction(new Name("fst"), r, s, t);
        frstr = new JavaDLFunction(new Name("frstr"), r, r, s, t);

        functions.add(frr);
        functions.add(f2rr);
        functions.add(fsr);
        functions.add(ftr);
        functions.add(fstr);
        functions.add(frstr);

        gss = new JavaDLFunction(new Name("gss"), s, s);
        grs = new JavaDLFunction(new Name("grs"), s, r);
        gts = new JavaDLFunction(new Name("gts"), s, t);
        grts = new JavaDLFunction(new Name("grts"), s, r, t);
        grsts = new JavaDLFunction(new Name("grsts"), s, r, s, t);

        functions.add(gss);
        functions.add(grs);
        functions.add(gts);
        functions.add(grts);
        functions.add(grsts);

        htt = new JavaDLFunction(new Name("htt"), t, t);
        hrt = new JavaDLFunction(new Name("hrt"), t, r);
        hst = new JavaDLFunction(new Name("hst"), t, s);
        hrst = new JavaDLFunction(new Name("hrst"), t, r, s);
        hrstt = new JavaDLFunction(new Name("hrstt"), t, r, s, t);

        functions.add(htt);
        functions.add(hrt);
        functions.add(hst);
        functions.add(hrst);
        functions.add(hrstt);

        // Formula function
        pp = new JavaDLFunction(new Name("pp"), JavaDLTheory.FORMULA, JavaDLTheory.FORMULA);
        pr = new JavaDLFunction(new Name("pr"), JavaDLTheory.FORMULA, r);
        ps = new JavaDLFunction(new Name("ps"), JavaDLTheory.FORMULA, s);
        pt = new JavaDLFunction(new Name("pt"), JavaDLTheory.FORMULA, t);
        prs = new JavaDLFunction(new Name("prs"), JavaDLTheory.FORMULA, r, s);
        prt = new JavaDLFunction(new Name("prt"), JavaDLTheory.FORMULA, r, t);
        pst = new JavaDLFunction(new Name("pst"), JavaDLTheory.FORMULA, s, t);
        prst = new JavaDLFunction(new Name("prst"), JavaDLTheory.FORMULA, r, s, t);
        // pi=new Function(new Name("pi"),Sort.FORMULA,new Sort[]{});
        functions.add(pp);
        functions.add(pr);
        functions.add(ps);
        functions.add(pt);
        functions.add(prs);
        functions.add(prt);
        functions.add(pst);
        functions.add(prst);
        // functions.add(pi);

        proof = new Proof("TestTriggersSet", TacletForTests.initConfig());
        g = new Goal(new Node(proof, Sequent.EMPTY_SEQUENT),
            TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());
        proof.setRoot(g.node());
        proof.add(g);

        proof.setNamespaces(new NamespaceSet(variables, functions, sorts, new Namespace<>(),
            new Namespace<>(), new Namespace<>()));

    }

    private Term parseTerm(String termstr) {
        return TacletForTests.parseTerm(termstr, new NamespaceSet(variables, functions, sorts,
            new Namespace<>(), new Namespace<>(), new Namespace<>()));
    }

    @Test
    public void testTrigger1() {
        String term1 = "\\forall s x;(ps(x))";
        Term allterm = parseTerm(term1);
        Term trigger1 = allterm.sub(0);
        TriggersSet ts = TriggersSet.create(allterm, proof.getServices());
        int triggerNum = ts.getAllTriggers().size();
        assertEquals(1, triggerNum);
        Term trigger2 = ts.getAllTriggers().iterator().next().getTriggerTerm();
        assertEquals(trigger1, trigger2);
    }

    @Test
    @Disabled("See Issues #1499")
    public void testTrigger2() {
        String term1 = "\\forall r x;(frr(x)=frr(frr(x)))";
        Term allterm = parseTerm(term1);
        Term trigger1 = allterm.sub(0).sub(1);
        TriggersSet ts = TriggersSet.create(allterm, proof.getServices());
        int triggerNum = ts.getAllTriggers().size();
        assertEquals(1, triggerNum);
        Term trigger2 = ts.getAllTriggers().iterator().next().getTriggerTerm();
        assertEquals(trigger1, trigger2);
    }
}
