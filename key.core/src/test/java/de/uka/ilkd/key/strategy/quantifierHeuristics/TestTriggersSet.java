/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;


// most Code are copyed from Logic.TestUpdateFactory

public class TestTriggersSet {

    private Proof proof;

    private final Namespace<QuantifiableVariable> variables = new Namespace<>();

    private final Namespace<Function> functions = new Namespace<>();

    private final Namespace<Sort> sorts = new Namespace<>();

    // sort
    private Sort r;
    private Sort s;
    private Sort t;
    // private Sort ints ;


    // constant function
    private Function r_a;
    private Function r_b;
    private Function r_c;

    private Function s_a;
    private Function s_b;
    private Function s_c;

    private Function t_a;
    private Function t_b;
    private Function t_c;

    // Rigid function
    private Function frr; // r->r
    private Function f2rr; // r->r
    private Function fsr; // s-> r
    private Function ftr; // t->r
    private Function fstr;// s->t->r
    private Function frstr;// r->s->t->r;

    private Function gss; // s->s
    private Function grs; // r->s
    private Function gts; // t->s
    private Function grts; // r->t->s
    private Function grsts;// r->s->t->s

    private Function htt; // t->t
    private Function hrt; // r -> t
    private Function hst; // s->t
    private Function hrst;// r->s->t
    private Function hrstt;// t->s->t->t

    // Formular function
    private Function pp;// Formula->Formula
    private Function pr;// r->Formula
    private Function ps;// s->Formula
    private Function pt;// t->Formula
    private Function prs;// r->s->Formula
    private Function pst;// s->t->Formula
    private Function prt;// r->t->Formula
    private Function prst;// r->s->t->Formula
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
        r_a = new Function(new Name("r_a"), r, new Sort[0]);
        r_b = new Function(new Name("r_b"), r, new Sort[0]);
        r_c = new Function(new Name("r_c"), r, new Sort[0]);
        functions.add(r_a);
        functions.add(r_b);
        functions.add(r_c);

        s_a = new Function(new Name("s_a"), s, new Sort[0]);
        s_b = new Function(new Name("s_b"), s, new Sort[0]);
        s_c = new Function(new Name("s_c"), s, new Sort[0]);
        functions.add(s_a);
        functions.add(s_b);
        functions.add(s_c);

        t_a = new Function(new Name("t_a"), s, new Sort[0]);
        t_b = new Function(new Name("t_b"), s, new Sort[0]);
        t_c = new Function(new Name("t_c"), s, new Sort[0]);
        functions.add(t_a);
        functions.add(t_b);
        functions.add(t_c);


        // function
        frr = new Function(new Name("frr"), r, r);
        f2rr = new Function(new Name("f2rr"), r, r);
        fsr = new Function(new Name("fsr"), r, s);
        ftr = new Function(new Name("ftr"), r, t);
        fstr = new Function(new Name("fst"), r, s, t);
        frstr = new Function(new Name("frstr"), r, r, s, t);

        functions.add(frr);
        functions.add(f2rr);
        functions.add(fsr);
        functions.add(ftr);
        functions.add(fstr);
        functions.add(frstr);

        gss = new Function(new Name("gss"), s, s);
        grs = new Function(new Name("grs"), s, r);
        gts = new Function(new Name("gts"), s, t);
        grts = new Function(new Name("grts"), s, r, t);
        grsts = new Function(new Name("grsts"), s, r, s, t);

        functions.add(gss);
        functions.add(grs);
        functions.add(gts);
        functions.add(grts);
        functions.add(grsts);

        htt = new Function(new Name("htt"), t, t);
        hrt = new Function(new Name("hrt"), t, r);
        hst = new Function(new Name("hst"), t, s);
        hrst = new Function(new Name("hrst"), t, r, s);
        hrstt = new Function(new Name("hrstt"), t, r, s, t);

        functions.add(htt);
        functions.add(hrt);
        functions.add(hst);
        functions.add(hrst);
        functions.add(hrstt);

        // Formula function
        pp = new Function(new Name("pp"), Sort.FORMULA, Sort.FORMULA);
        pr = new Function(new Name("pr"), Sort.FORMULA, r);
        ps = new Function(new Name("ps"), Sort.FORMULA, s);
        pt = new Function(new Name("pt"), Sort.FORMULA, t);
        prs = new Function(new Name("prs"), Sort.FORMULA, r, s);
        prt = new Function(new Name("prt"), Sort.FORMULA, r, t);
        pst = new Function(new Name("pst"), Sort.FORMULA, s, t);
        prst = new Function(new Name("prst"), Sort.FORMULA, r, s, t);
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
