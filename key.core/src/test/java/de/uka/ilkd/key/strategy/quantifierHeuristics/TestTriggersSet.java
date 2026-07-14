/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


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
        r_a = new JFunction(new Name("r_a"), r, new Sort[0]);
        r_b = new JFunction(new Name("r_b"), r, new Sort[0]);
        r_c = new JFunction(new Name("r_c"), r, new Sort[0]);
        functions.add(r_a);
        functions.add(r_b);
        functions.add(r_c);

        s_a = new JFunction(new Name("s_a"), s, new Sort[0]);
        s_b = new JFunction(new Name("s_b"), s, new Sort[0]);
        s_c = new JFunction(new Name("s_c"), s, new Sort[0]);
        functions.add(s_a);
        functions.add(s_b);
        functions.add(s_c);

        t_a = new JFunction(new Name("t_a"), s, new Sort[0]);
        t_b = new JFunction(new Name("t_b"), s, new Sort[0]);
        t_c = new JFunction(new Name("t_c"), s, new Sort[0]);
        functions.add(t_a);
        functions.add(t_b);
        functions.add(t_c);


        // function
        frr = new JFunction(new Name("frr"), r, r);
        f2rr = new JFunction(new Name("f2rr"), r, r);
        fsr = new JFunction(new Name("fsr"), r, s);
        ftr = new JFunction(new Name("ftr"), r, t);
        fstr = new JFunction(new Name("fst"), r, s, t);
        frstr = new JFunction(new Name("frstr"), r, r, s, t);

        functions.add(frr);
        functions.add(f2rr);
        functions.add(fsr);
        functions.add(ftr);
        functions.add(fstr);
        functions.add(frstr);

        gss = new JFunction(new Name("gss"), s, s);
        grs = new JFunction(new Name("grs"), s, r);
        gts = new JFunction(new Name("gts"), s, t);
        grts = new JFunction(new Name("grts"), s, r, t);
        grsts = new JFunction(new Name("grsts"), s, r, s, t);

        functions.add(gss);
        functions.add(grs);
        functions.add(gts);
        functions.add(grts);
        functions.add(grsts);

        htt = new JFunction(new Name("htt"), t, t);
        hrt = new JFunction(new Name("hrt"), t, r);
        hst = new JFunction(new Name("hst"), t, s);
        hrst = new JFunction(new Name("hrst"), t, r, s);
        hrstt = new JFunction(new Name("hrstt"), t, r, s, t);

        functions.add(htt);
        functions.add(hrt);
        functions.add(hst);
        functions.add(hrst);
        functions.add(hrstt);

        // Formula function
        pp = new JFunction(new Name("pp"), JavaDLTheory.FORMULA, JavaDLTheory.FORMULA);
        pr = new JFunction(new Name("pr"), JavaDLTheory.FORMULA, r);
        ps = new JFunction(new Name("ps"), JavaDLTheory.FORMULA, s);
        pt = new JFunction(new Name("pt"), JavaDLTheory.FORMULA, t);
        prs = new JFunction(new Name("prs"), JavaDLTheory.FORMULA, r, s);
        prt = new JFunction(new Name("prt"), JavaDLTheory.FORMULA, r, t);
        pst = new JFunction(new Name("pst"), JavaDLTheory.FORMULA, s, t);
        prst = new JFunction(new Name("prst"), JavaDLTheory.FORMULA, r, s, t);
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
        g = new Goal(new Node(proof, JavaDLSequentKit.getInstance().getEmptySequent()),
            TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());
        proof.setRoot(g.node());
        proof.add(g);

        proof.setNamespaces(
            new NamespaceSet(variables, functions, sorts, new Namespace<>(), new Namespace<>(),
                new Namespace<>(), new Namespace<>(),
                new Namespace<>(), new Namespace<>()));

    }

    private JTerm parseTerm(String termstr) {
        return TacletForTests.parseTerm(termstr,
            new NamespaceSet(variables, functions, sorts, new Namespace<>(), new Namespace<>(),
                new Namespace<>(),
                new Namespace<>(), new Namespace<>(), new Namespace<>()));
    }

    @Test
    public void testTrigger1() {
        String term1 = "\\forall s x;(ps(x))";
        JTerm allterm = parseTerm(term1);
        JTerm trigger1 = allterm.sub(0);
        TriggersSet ts = TriggersSet.create(allterm, proof.getServices());
        int triggerNum = ts.getAllTriggers().size();
        assertEquals(1, triggerNum);
        var trigger2 = ts.getAllTriggers().iterator().next().getTriggerTerm();
        assertEquals(trigger1, trigger2);
    }

    // --- Characterization tests ---------------------------------------------------------------
    // These pin the CURRENT trigger-set output to guard the cleanup/restructure refactor; they are
    // a behavior-preservation net, NOT a statement that the current output is ideal. Cases marked
    // "SCRUTINIZE" are deliberate-tuning candidates for the later inequality/specificity step and
    // must not be treated as desirable behavior to keep forever.

    private ImmutableSet<Trigger> triggersOf(String formula) {
        return TriggersSet.create(parseTerm(formula), proof.getServices()).getAllTriggers();
    }

    @Test
    public void existentialInnerVariableYieldsUniTrigger() {
        // forall x. exists y. prs(x,y): the existential variable is carried in the trigger; still a
        // single uni-trigger (matched two-sidedly because it contains a non-universal variable).
        final JTerm all = parseTerm("\\forall r x;(\\exists s y;(prs(x,y)))");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(1, triggers.size());
        assertEquals(all.sub(0).sub(0), triggers.iterator().next().getTriggerTerm()); // prs(x,y)
    }

    @Test
    public void conjunctionYieldsOneTriggerPerClause() {
        // forall x. (pr(x) & pr(frr(x))): the matrix is AND-split into two clauses, each
        // contributing its own trigger.
        final JTerm all = parseTerm("\\forall r x;(pr(x) & pr(frr(x)))");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(2, triggers.size());
        final Set<Term> expected = new HashSet<>();
        expected.add(all.sub(0).sub(0)); // pr(x)
        expected.add(all.sub(0).sub(1).sub(0)); // frr(x) inside pr(frr(x))
        final Set<Term> actual = new HashSet<>();
        for (Trigger tr : triggers) {
            actual.add(tr.getTriggerTerm());
        }
        assertEquals(expected, actual);
    }

    @Test
    public void bodyWithoutOuterVariableHasNoTriggers() {
        // forall x. forall y. ps(y): no literal mentions the OUTER variable x, so the
        // first-variable
        // requirement rejects every candidate -> no triggers at all. (Refactor-fragile invariant.)
        final ImmutableSet<Trigger> triggers = triggersOf("\\forall r x;(\\forall s y;(ps(y)))");
        assertEquals(0, triggers.size());
    }

    @Test
    public void negatedGuardLiteralTriggersFromGuard() {
        // The canonical quantifier shape forall x. (!guard | post) == (guard -> post): the NOT
        // is stripped, so triggers come from BOTH the guard and the post (here frr(x) and pr(x)).
        final JTerm all = parseTerm("\\forall r x;(!pr(frr(x)) | pr(x))");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(2, triggers.size());
        final Set<Term> expected = new HashSet<>();
        expected.add(all.sub(0).sub(0).sub(0).sub(0)); // frr(x), inside !pr(frr(x))
        expected.add(all.sub(0).sub(1)); // pr(x)
        final Set<Term> actual = new HashSet<>();
        for (Trigger tr : triggers) {
            assertTrue(tr instanceof UniTrigger);
            actual.add(tr.getTriggerTerm());
        }
        assertEquals(expected, actual);
    }

    @Test
    public void negatedLiteralParticipatesInMultiTrigger() {
        // forall x,y. (!pr(x) | ps(y)): the negated guard (covering only x) joins ps(y) in one
        // multi-trigger; the clause term keeps the negation, the matched element strips it.
        final ImmutableSet<Trigger> triggers =
            triggersOf("\\forall r x;(\\forall s y;(!pr(x) | ps(y)))");
        assertEquals(1, triggers.size());
        assertTrue(triggers.iterator().next() instanceof MultiTrigger);
    }

    @Test
    public void uniTriggerDescendsPastPredicate() {
        // pr(frr(x)) -> the term argument frr(x), not the predicate literal.
        final JTerm all = parseTerm("\\forall r x;(pr(frr(x)))");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(1, triggers.size());
        assertEquals(all.sub(0).sub(0), triggers.iterator().next().getTriggerTerm()); // frr(x)
    }

    @Test
    public void uniTriggerPicksInnermostSubterm() {
        // pr(frr(f2rr(x))) -> f2rr(x): descends to the INNERMOST subterm still containing the bound
        // variable, i.e. a very general trigger. SCRUTINIZE (over-general -> excess instantiation).
        final JTerm all = parseTerm("\\forall r x;(pr(frr(f2rr(x))))");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(1, triggers.size());
        assertEquals(all.sub(0).sub(0).sub(0), triggers.iterator().next().getTriggerTerm()); // f2rr(x)
    }

    @Test
    public void fullCoverUniTriggerPreferredOverElements() {
        // prs(x,y) covers both clause variables -> single uni-trigger; partial pr(x) is dropped.
        final JTerm all = parseTerm("\\forall r x;(\\forall s y;(prs(x,y) | pr(x)))");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(1, triggers.size());
        final Trigger only = triggers.iterator().next();
        assertTrue(only instanceof UniTrigger);
        assertEquals(all.sub(0).sub(0).sub(0), only.getTriggerTerm()); // prs(x,y)
    }

    @Test
    public void multiTriggerAcrossLiterals() {
        // pr(x) | ps(y): neither literal covers {x,y} -> one multi-trigger over the clause.
        final ImmutableSet<Trigger> triggers =
            triggersOf("\\forall r x;(\\forall s y;(pr(x) | ps(y)))");
        assertEquals(1, triggers.size());
        assertTrue(triggers.iterator().next() instanceof MultiTrigger);
    }

    @Test
    public void multiTriggerPowersetEnumeratesCoveringCombinations() {
        // pr(x) | pr(frr(x)) | ps(y): the two x-elements {pr(x), frr(x)} each combine with ps(y)
        // into TWO minimal covering multi-triggers (supersets pruned). Pins the powerset
        // cardinality
        // so the restructure step must preserve it.
        final ImmutableSet<Trigger> triggers =
            triggersOf("\\forall r x;(\\forall s y;(pr(x) | pr(frr(x)) | ps(y)))");
        assertEquals(2, triggers.size());
        for (Trigger tr : triggers) {
            assertTrue(tr instanceof MultiTrigger);
        }
    }

    @Test
    public void equalityExcludedButSubtermStillTriggers() {
        // frr(x) = r_a: the equality op is excluded (isAcceptableTrigger), but subterm frr(x) still
        // triggers. Pins the equality handling, relevant to the later inequality knob. SCRUTINIZE.
        final JTerm all = parseTerm("\\forall r x;(frr(x) = r_a)");
        final ImmutableSet<Trigger> triggers =
            TriggersSet.create(all, proof.getServices()).getAllTriggers();
        assertEquals(1, triggers.size());
        assertEquals(all.sub(0).sub(0), triggers.iterator().next().getTriggerTerm()); // frr(x)
    }

    @Test
    @Disabled("See Issues #1499")
    public void testTrigger2() {
        String term1 = "\\forall r x;(frr(x)=frr(frr(x)))";
        JTerm allterm = parseTerm(term1);
        JTerm trigger1 = allterm.sub(0).sub(1);
        TriggersSet ts = TriggersSet.create(allterm, proof.getServices());
        int triggerNum = ts.getAllTriggers().size();
        assertEquals(1, triggerNum);
        var trigger2 = ts.getAllTriggers().iterator().next().getTriggerTerm();
        assertEquals(trigger1, trigger2);
    }
}
