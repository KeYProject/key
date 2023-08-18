/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.io.IOException;
import java.util.Stack;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.AbstractTestTermParser;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class TestClashFreeSubst extends AbstractTestTermParser {

    TermFactory tf;

    Services services;
    NamespaceSet nss;

    Sort srt;

    Function f, g;
    Function p, q;

    LogicVariable v, x, y, z;
    Term t_v, t_x, t_y, t_z;

    ProgramVariable pv0;

    @BeforeEach
    public void setUp() throws IOException {
        services = new Services(AbstractProfile.getDefaultProfile());
        nss = services.getNamespaces();
        tf = services.getTermFactory();
        io = new KeyIO(services, nss);
        String sorts = "\\sorts{boolean;int;LocSet;Seq;double;float;}";
        parseDecls(sorts);
        assertNotNull(nss.sorts().lookup("boolean"));

        Recoder2KeY r2k = new Recoder2KeY(services, nss);
        r2k.parseSpecialClasses();

        parseDecls(
            "\\sorts { srt; }\n" + "\\functions {\n" + "  srt f(srt);\n" + "  srt g(srt,srt);\n"
                + "}\n" + "\\predicates {\n" + "  p(srt);\n" + "  q(srt,srt);\n" + "}");

        srt = lookup_sort("srt");


        f = lookup_func("f");
        g = lookup_func("g");
        p = lookup_func("p");
        q = lookup_func("q");
        pv0 = new LocationVariable(new ProgramElementName("pv0"), srt);
        nss.programVariables().add(pv0);

        // The declaration parser cannot parse LogicVariables; these
        // are normally declared in quantifiers, so we introduce them
        // ourselves!
        v = declareVar("v", srt);
        t_v = tf.createTerm(v);
        x = declareVar("x", srt);
        t_x = tf.createTerm(x);
        y = declareVar("y", srt);
        t_y = tf.createTerm(y);
        z = declareVar("z", srt);
        t_z = tf.createTerm(z);
    }

    public Sort lookup_sort(String name) {
        Sort s = nss.sorts().lookup(new Name(name));
        if (s == null) {
            throw new RuntimeException("Sort named " + name + " not found");
        }
        return s;
    }

    public Function lookup_func(String name) {
        Function f = nss.functions().lookup(new Name(name));
        if (f == null) {
            throw new RuntimeException("Function named " + name + " not found");
        }
        return f;
    }

    public LogicVariable declareVar(String name, Sort sort) {
        LogicVariable v = new LogicVariable(new Name(name), sort);
        nss.variables().add(v);
        return v;
    }


    /**
     * transform sequences all x. all y. ... bla to all x,y... . bla). no rulevars, no javaBlocks.
     */
    private Term toMulti(Term t) {
        ToMultiVisitor v = new ToMultiVisitor();
        t.execPostOrder(v);
        return v.getResult();
    }

    private class ToMultiVisitor extends DefaultVisitor {
        private final Stack<Term> subStack;

        ToMultiVisitor() {
            subStack = new Stack<>();
        }

        public void visit(Term visited) {
            Operator op = visited.op();
            int arity = visited.arity();
            if (op == Quantifier.ALL) {
                Term top = subStack.peek();
                if (top.op() == Quantifier.ALL) {
                    QuantifiableVariable[] bv =
                        new QuantifiableVariable[visited.varsBoundHere(0).size()
                                + top.varsBoundHere(0).size()];
                    for (int i = 0; i < visited.varsBoundHere(0).size(); i++) {
                        bv[i] = visited.varsBoundHere(0).get(i);
                    }
                    for (int i = 0; i < top.varsBoundHere(0).size(); i++) {
                        bv[visited.varsBoundHere(0).size() + i] = top.varsBoundHere(0).get(i);
                    }
                    subStack.pop();
                    subStack.push(TacletForTests.services().getTermBuilder().all(
                        ImmutableSLList.<QuantifiableVariable>nil().append(bv), top.sub(0)));
                    return;
                }
            }
            Term[] sub = new Term[arity];
            for (int i = arity - 1; i >= 0; i--) {
                sub[i] = subStack.pop();
            }
            subStack.push(tf.createTerm(op, sub, visited.boundVars(), null));
        }

        Term getResult() {
            return subStack.pop();
        }
    }

    // Test Cases

    @Test
    public void testSubst() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("g(v,x)");
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        assertEquals(parseTerm("g(f(x),x)"), cfs.apply(t), "substitution");
    }

    @Test
    public void testSubstWary() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("q(v,x)");
        WaryClashFreeSubst cfs = new WaryClashFreeSubst(v, s, services.getTermBuilder());
        assertEquals(parseTerm("q(f(x),x)"), cfs.apply(t), "substitution");
    }

    @Test
    public void testShare() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("g(v,f(x))");
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        assertSame(t.sub(1), cfs.apply(t).sub(1), "share unchanged subterms");
    }

    @Test
    public void testShareWary() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("q(v,f(x))");
        WaryClashFreeSubst cfs = new WaryClashFreeSubst(v, s, services.getTermBuilder());
        assertSame(t.sub(1), cfs.apply(t).sub(1), "share unchanged subterms");
    }

    /*
     * public void testShareBound() { Term s = parseTerm("f(x)"); Term t =
     * parseTerm("g(v,eps v.q(x,v))"); ClashFreeSubst cfs = new ClashFreeSubst(v,s);
     * assertSame("sharing with bound variables", t.sub(1), cfs.apply(t).sub(1)); }
     *
     * public void testShareAll() { Term s = parseTerm("f(x)"); Term t =
     * parseTerm("eps x.g(x,eps v.q(x,v))"); ClashFreeSubst cfs = new ClashFreeSubst(v,s);
     * assertSame("sharing whole term despite clash", t, cfs.apply(t)); }
     */

    @Test
    public void testClash() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("\\exists x; q(x,v)");
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        Term res = cfs.apply(t);
        QuantifiableVariable x1 = res.varsBoundHere(0).get(0);
        Namespace<QuantifiableVariable> ns = new Namespace<>(nss.variables());
        ns.add(x1);
        nss.setVariables(ns);
        assertEquals(parseTerm("\\exists x1; q(x1,f(x))"), res, "clash resolution");
        nss.setVariables(nss.variables().parent());
    }

    @Test
    public void testSubstInSubstTerm() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("{\\subst y; f(v)}g(y,v)");
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        assertEquals(parseTerm("{\\subst y; f(f(x))}g(y,f(x))"), cfs.apply(t),
            "substitute into substitution term");
    }

    @Test
    public void testClashInSubstTerm() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = parseTerm("{\\subst x; f(v)}g(x,v)");
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        Term res = cfs.apply(t);
        QuantifiableVariable x1 = res.varsBoundHere(1).get(0);
        Namespace<QuantifiableVariable> ns = new Namespace<>(nss.variables());
        ns.add(x1);
        nss.setVariables(ns);
        assertEquals(parseTerm("{\\subst x1; f(f(x))}g(x1,f(x))"), res,
            "clash resolution in substitution term");
        nss.setVariables(nss.variables().parent());
    }


    @Test
    public void testMultiSubst() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = toMulti(parseFma("\\forall y; \\forall z; q(y,g(v,z))"));
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        assertEquals(toMulti(parseFma("\\forall y; \\forall z; q(y,g(f(x),z))")), cfs.apply(t),
            "substitution on multi");
    }

    private Term parseFma(String s) throws Exception { return parseTerm(s); }

    @Test
    public void testMultiShareBound() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = toMulti(parseFma("\\forall y; \\forall v; \\forall z; q(y,g(v,z))"));
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        assertSame(cfs.apply(t), t, "sharing on multi");
    }

    // disabled. multi vars at quantifier currently not supported by
    // KeY and feature of data structures suppressed by TermFactory. /AR 040420
    @Test
    @Disabled
    public void xtestMultiClash() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = toMulti(parseFma("\\forall y; \\forall x; \\forall z; q(g(x,y),g(v,z))"));
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        Term res = cfs.apply(t);
        QuantifiableVariable x1 = res.varsBoundHere(0).get(1);
        Namespace<QuantifiableVariable> ns = new Namespace<>(nss.variables());
        ns.add(x1);
        nss.setVariables(ns);
        assertEquals(
            toMulti(parseTerm("\\forall y; \\forall x1; \\forall z; q(g(x1,y),g(f(x),z))")), res,
            "clash resolution in multi term");
        nss.setVariables(nss.variables().parent());
    }

    // disabled. multi vars at quantifier currently not supported by
    // KeY and feature of data structures suppressed by TermFactory. /AR 040420
    @Test
    @Disabled
    public void xtestMultiClash1() throws Exception {
        Term s = parseTerm("f(x)");
        Term t = toMulti(parseFma("\\forall y; \\forall x;\\forall z; q(g(x,y),g(v,z))"));
        ClashFreeSubst cfs = new ClashFreeSubst(v, s, services.getTermBuilder());
        Term res = cfs.apply(t);
        QuantifiableVariable x1 = res.varsBoundHere(0).get(2);
        Namespace<QuantifiableVariable> ns = new Namespace<>(nss.variables());
        ns.add(x1);
        nss.setVariables(ns);
        assertEquals(toMulti(parseTerm("q(g(x1,y),g(f(x),z))")), res.sub(0),
            "clash resolution in multi term");
        nss.setVariables(nss.variables().parent());
    }


    @Test
    public void testWary0() throws Exception {
        Term s = parseTerm("f(pv0)");
        Term t = parseTerm("q(v,x)");
        WaryClashFreeSubst cfs = new WaryClashFreeSubst(v, s, services.getTermBuilder());
        assertEquals(parseTerm("q(f(pv0),x)"), cfs.apply(t), "substitution");
    }

    @Test
    public void testWary1() throws Exception {
        Term s = parseTerm("f(pv0)");
        Term t = parseTerm("q(v,x) & {pv0:=v}q(x,x)");
        WaryClashFreeSubst cfs = new WaryClashFreeSubst(v, s, services.getTermBuilder());
        assertEquals(parseTerm("q(f(pv0),x) & {pv0:=f(pv0)}q(x,x)"), cfs.apply(t), "substitution");
    }

    @Test
    public void testWary2() throws Exception {
        Term s = parseTerm("f(pv0)");
        Term t = parseTerm("q(v,x) & {pv0:=v}q(x,v)");
        WaryClashFreeSubst cfs = new WaryClashFreeSubst(v, s, services.getTermBuilder());
        Term res = cfs.apply(t);
        QuantifiableVariable x1 = res.varsBoundHere(1).get(0);
        Namespace<QuantifiableVariable> ns = new Namespace<>(nss.variables());
        ns.add(x1);
        nss.setVariables(ns);
        assertEquals(parseTerm("{\\subst " + x1.name()
            + "; f(pv0)} ( q(f(pv0),x) & {pv0:=f(pv0)}q(x," + x1.name() + ") )"), cfs.apply(t),
            "substitution");
        nss.setVariables(nss.variables().parent());
    }
}
