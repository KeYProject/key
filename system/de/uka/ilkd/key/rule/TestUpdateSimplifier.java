// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.io.File;
import java.util.Arrays;
import java.util.LinkedList;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.util.HelperClassForTests;

/**
 * Class used for testing the simultaneous update simplifier. ATTENTION: If
 * <code>assertSame</code> is used, do not replace this test with
 * <code>assertEquals</code> without thinking, as we test here also if the
 * memory resources are wasted or not.
 */
public class TestUpdateSimplifier extends TestCase {

    private Namespace variables;

    private Namespace functions;

    private Namespace sorts;

    private ProgramVariable[] pv;

    private ProgramVariable spv;

    private static final TermBuilder TB = TermBuilder.DF;

    private Sort testSort0;

    private Sort testSort1;

    private Sort testSort2;

    private Sort cloneable;

    private Sort serializable;

    private Sort integerSort;

    // t : testSort1
    private Term t;

    // i : testSort1
    private Term i;

    // o : testSort1
    private Term o;

    // u : testSort1
    private Term u;

    // r: testSort2
    private Term r;

    // o.a
    private Term oa;

    // u.a
    private Term ua;

    // r.a
    private Term ra;

    // o.spv (spv static attribute)
    private Term ospv;

    // u.spv (spv static attribute)
    private Term uspv;

    // arrays
    private ArraySort arraySort1;

    private ArraySort arraySort2;

    private Term a;

    private Term b;

    private Term c;

    // integers
    private Term idx;

    private Term jdx;

    private Term mdx;

    // a[idx] : array of testSort 1
    private Term ai;

    // a[jdx] : array of testSort 1
    private Term aj;

    // a[mdx] : array of testSort 1
    private Term am;

    // b[idx] : array of testSort 1
    private Term bi;

    // b[jdx] : array of testSort 1
    private Term bj;

    // c[idx] : array of testSort 2
    private Term ci;

    // c[jdx] : array of testSort 2
    private Term cj;

    // variables

    // variable of sort arraySort1
    private LogicVariable arrayVar1;

    // variables of sort integer
    private LogicVariable intVar;

    public TestUpdateSimplifier(String s) {
	super(s);
    }

//    /**
//     * creates an update term where the given locations are updated this method
//     * requires detailed knowledge of the update structure as the subterms must
//     * have the correct order.
//     * 
//     * @param locations
//     *                the Location operators of the update
//     * @param subs
//     *                the array of Term with the subterms of the locations to be
//     *                updated, the values and the target term
//     * @return the above described update term
//     */
//    public Term createUpdateTerm(Location[] locations, Term[] subs) {
//	final boolean guards[] = new boolean[locations.length];
//	Arrays.fill(guards, false);
//
//	final QuanUpdateOperator op = QuanUpdateOperator.createUpdateOp(
//		locations, guards);
//
//	final ArrayOfQuantifiableVariable[] bv = new ArrayOfQuantifiableVariable[subs.length];
//	Arrays.fill(bv, new ArrayOfQuantifiableVariable());
//
//	return op.normalize(bv, subs);
//    }
//
//    private Term createUpdateTerm(Term[] subs) {
//	Location[] loc = new Location[(subs.length - 1) / 2];
//	LinkedList newSubs = new LinkedList();
//	int count = 0;
//	for (int i1 = 0; i1 < subs.length - 2; i1 += 2, count++) {
//	    loc[count] = (Location) subs[i1].op();
//	    for (int j = 0; j < subs[i1].arity(); j++) {
//		newSubs.add(subs[i1].sub(j));
//	    }
//	    newSubs.add(subs[i1 + 1]);
//	}
//	newSubs.add(subs[subs.length - 1]);
//	return createUpdateTerm(loc, (Term[]) newSubs.toArray(new Term[0]));
//    }
//
//    private void assertEqualsModRenaming(Term t1, Term expected) {
//	assertTrue("Expected " + expected + ", but got " + t1, t1
//		.equalsModRenaming(expected));
//    }
//
//    public void setUp() {
//	variables = new Namespace();
//	functions = new Namespace();
//	sorts = new Namespace();
//	AbstractSort intSort = new PrimitiveSort(new Name("int"));
//	AbstractSort booleanSort = new PrimitiveSort(new Name("boolean"));
//	sorts.add(intSort);
//	sorts.add(booleanSort);
//
//	intSort.addDefinedSymbols(functions, sorts);
//	booleanSort.addDefinedSymbols(functions, sorts);
//
//	testSort0 = new ClassInstanceSortImpl(new Name("testSort0"), false);
//	testSort1 = new ClassInstanceSortImpl(new Name("testSort1"), testSort0,
//		false);
//	testSort2 = new ClassInstanceSortImpl(new Name("testSort2"), testSort0,
//		false);
//	cloneable = new ClassInstanceSortImpl(new Name("cloneable"), testSort1,
//		true);
//	serializable = new ClassInstanceSortImpl(new Name("serializable"),
//		testSort1, true);
//
//	((AbstractSort) testSort0).addDefinedSymbols(functions, sorts);
//	((AbstractSort) testSort1).addDefinedSymbols(functions, sorts);
//	((AbstractSort) testSort2).addDefinedSymbols(functions, sorts);
//	((AbstractSort) cloneable).addDefinedSymbols(functions, sorts);
//	((AbstractSort) serializable).addDefinedSymbols(functions, sorts);
//
//	KeYJavaType kjt = new KeYJavaType(new ClassDeclaration(
//		new ProgramElementName("Object"), new ProgramElementName(
//			"java.lang.Object")), testSort1);
//	sorts.add(testSort0);
//	sorts.add(testSort1);
//	sorts.add(testSort2);
//	sorts.add(cloneable);
//	sorts.add(serializable);
//
//	pv = new ProgramVariable[7];
//	for (int i1 = 0; i1 < pv.length; i1++) {
//	    ProgramElementName name;
//	    switch (i1) {
//	    case 1:
//		name = new ProgramElementName("t");
//		break;
//	    case 2:
//		name = new ProgramElementName("i");
//		break;
//	    case 3:
//		name = new ProgramElementName("o");
//		break;
//	    case 4:
//		name = new ProgramElementName("u");
//		break;
//	    case 5:
//		name = new ProgramElementName("a");
//		break;
//	    default:
//		name = new ProgramElementName("pv" + i1);
//		break;
//	    }
//	    if (i1 == 5) {
//		pv[i1] = new LocationVariable(name, kjt, kjt, false);
//	    } else {
//		pv[i1] = new LocationVariable(name, kjt);
//	    }
//	    variables.add(pv[i1]);
//	}
//
//	spv = new LocationVariable(new ProgramElementName("spv"), kjt, kjt,
//		true);
//
//	// just initialize the parser
//	parseTerm("{t:=i} o");
//	// for the systematic tests
//
//	t = TB.var(pv[1]);
//	i = TB.var(pv[2]);
//	o = TB.var(pv[3]);
//	u = TB.var(pv[4]);
//	ProgramVariable r_var = new LocationVariable(
//		new ProgramElementName("r"), testSort2);
//	r = TB.var(r_var);
//
//	oa = TB.dot(o, pv[5]);
//	ua = TB.dot(u, pv[5]);
//	ra = TB.dot(r, pv[5]);
//
//	ospv = TB.dot(o, spv);
//	uspv = TB.dot(u, spv);
//
//	arraySort1 = ArraySortImpl.getArraySort(testSort1, testSort0,
//		cloneable, serializable);
//	arraySort2 = ArraySortImpl.getArraySort(testSort2, testSort0,
//		cloneable, serializable);
//
//	final KeYJavaType kjt1 = new KeYJavaType(arraySort1);
//	final KeYJavaType kjt2 = new KeYJavaType(arraySort2);
//
//	ProgramVariable a_var = new LocationVariable(new ProgramElementName(
//		"_a"), kjt1);
//	ProgramVariable b_var = new LocationVariable(new ProgramElementName(
//		"_b"), kjt1);
//	ProgramVariable c_var = new LocationVariable(new ProgramElementName(
//		"_c"), kjt2);
//
//	a = TB.var(a_var);
//	b = TB.var(b_var);
//	c = TB.var(c_var);
//
//	final Services services = TacletForTests.services();
//	integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
//	ProgramVariable idx_var = new LocationVariable(new ProgramElementName(
//		"i"), integerSort);
//	ProgramVariable jdx_var = new LocationVariable(new ProgramElementName(
//		"j"), integerSort);
//
//	ProgramVariable mdx_var = new LocationVariable(new ProgramElementName(
//		"m"), integerSort);
//
//	idx = TB.var(idx_var);
//	jdx = TB.var(jdx_var);
//	mdx = TB.var(mdx_var);
//
//	ai = TB.array(services, a, idx);
//	aj = TB.array(services, a, jdx);
//	am = TB.array(services, a, mdx);
//
//	bi = TB.array(services, b, idx);
//	bj = TB.array(services, b, jdx);
//
//	ci = TB.array(services, c, idx);
//	cj = TB.array(services, c, jdx);
//
//	arrayVar1 = new LogicVariable(new Name("arrayVar1"), arraySort1);
//	intVar = new LogicVariable(new Name("intVar"), integerSort);
//    }
//
//    public void tearDown() {
//	variables = null;
//	functions = null;
//	sorts = null;
//    }
//
//    private Term parseTerm(String termstr) {
//	return TacletForTests.parseTerm(termstr, new NamespaceSet(
//		new Namespace(), functions, sorts, new Namespace(),
//		new Namespace(), variables));
//    }
//
//    public void testBasicRules() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	Services services = TacletForTests.services();
//
//	Term parsed = parseTerm("{t:=i} o");
//	assertTrue(simply.simplify(parsed, services) == parsed.sub(parsed
//		.arity() - 1));
//
//	parsed = parseTerm("{t:=i} t");
//	assertTrue(simply.simplify(parsed, services) == parsed.sub(parsed
//		.arity() - 2));
//
//	parsed = parseTerm("{t:=i || i:=o} t");
//	assertTrue(simply.simplify(parsed, services).op() == pv[2]);
//
//	Term[] subs = new Term[parsed.arity()];
//	for (int i = 0; i < parsed.arity() - 1; i++) {
//	    subs[i] = parsed.sub(i);
//	}
//	subs[parsed.arity() - 1] = TB.dot(TB.var(pv[4]), pv[5]);
//
//	// {t:=i, i:=o} u.a ~~~> u.a
//	Term constr = createUpdateTerm(new Term[] { t, i, i, o, ua });
//	Term simplified = simply.simplify(constr, services);
//	Term expected = ua;
//	assertEquals("Failed applying {t:=i, i:=o} u.a", expected, simplified);
//	assertSame("Failed applying  {t:=i, i:=o} u.a (wasted memory)",
//		expected, simplified);
//
//	// {i:=t, o.a:=i} u.a ~~~>(u?=o).a/->i
//	constr = createUpdateTerm(new Term[] { i, t, oa, i, ua });
//	simplified = simply.simplify(constr, services);
//	// expected = tf.createIfElseTerm(u, o, i, ua);
//	expected = TB.ife(TB.equals(u, o), i, ua);
//
//	assertEquals("Failed applying {i:=t || o.a:=i} u.a", expected,
//		simplified);
//
//	assertSame("Failed applying {i:=t || o.a:=i} u.a (memory wasted)", u,
//		simplified.sub(0).sub(0));
//	assertSame("Failed applying {i:=t || o.a:=i} u.a (memory wasted)", o,
//		simplified.sub(0).sub(1));
//	assertSame("Failed applying {i:=t || o.a:=i} u.a (memory wasted)", i,
//		simplified.sub(1));
//	assertSame("Failed applying {i:=t || o.a:=i} u.a (memory wasted)", ua,
//		simplified.sub(2));
//
//	// {o.a:=u, u.a:=i} t.a ---> (t ?= u) i : (t ?= o) u : t.a
//	Term ta = TB.dot(t, pv[5]);
//	constr = createUpdateTerm(new Term[] { oa, u, ua, i, ta });
//	simplified = simply.simplify(constr, services);
//	// expected = tf.createIfElseTerm
//	// (t, u, i, tf.createIfElseTerm(t, o, u, ta));
//	expected = TB.ife(TB.equals(t, u), i, TB.ife(TB.equals(t, o), u, ta));
//
//	assertEquals("Failed applying {o.a:=u, u.a:=i} t.a", expected,
//		simplified);
//	for (int i = 0; i < expected.arity(); i++) {
//	    assertSame("Memory waste detected", expected.sub(0).sub(0),
//		    simplified.sub(0).sub(0));
//	    assertSame("Memory waste detected", expected.sub(0).sub(1),
//		    simplified.sub(0).sub(1));
//	    assertSame("Memory waste detected", expected.sub(1), simplified
//		    .sub(1));
//	    assertSame("Memory waste detected", expected.sub(2).sub(0).sub(0),
//		    simplified.sub(2).sub(0).sub(0));
//	    assertSame("Memory waste detected", expected.sub(2).sub(0).sub(1),
//		    simplified.sub(2).sub(0).sub(1));
//	    assertSame("Memory waste detected", expected.sub(2).sub(1),
//		    simplified.sub(2).sub(1));
//	    assertSame("Memory waste detected", expected.sub(2).sub(2),
//		    simplified.sub(2).sub(2));
//	}
//
//	// {t:=i} {i:=o, o:=t}<>true ~~> {t:=i, i:=o, o:=i}<>true
//	parsed = parseTerm("{t:=i} {i:=o || o:=t} \\<{}\\>true");
//	expected = parseTerm("{t:=i || i:=o || o:=i} \\<{}\\>true");
//	simplified = simply.simplify(parsed, services);
//	assertEquals("Failed applying {t:=i} {i:=o, o:=t}<>true", expected,
//		simplified);
//
//	// {t:=i} {t:=o, o:=t}<>true ~~> {t:=o, o:=i}<>true
//	parsed = parseTerm("{t:=i} {t:=o || o:=t} \\<{}\\>true");
//	expected = parseTerm("{t:=o || o:=i} \\<{}\\>true");
//	simplified = simply.simplify(parsed, services);
//	assertEquals("Failed applying {t:=i} {t:=o, o:=t}<>true", expected,
//		simplified);
//
//	// {i.a:=t, t.a:=i, u.a:=o} t.a = t ~~>
//	// ((t ?= u) o : i) = t
//	subs = new Term[7];
//	subs[0] = TB.dot(TB.var(pv[2]), pv[5]);
//	subs[1] = TB.var(pv[1]);
//	subs[2] = TB.dot(TB.var(pv[1]), pv[5]);
//	subs[3] = TB.var(pv[2]);
//	subs[4] = TB.dot(TB.var(pv[4]), pv[5]);
//	subs[5] = TB.var(pv[3]);
//	subs[6] = TB.equals(TB.dot(TB.var(pv[1]), pv[5]), TB.var(pv[1]));
//
//	constr = createUpdateTerm(subs);
//	expected = parseTerm("\\if (t = u) \\then (o) \\else (i)");
//
//	Term[] e_subs = new Term[expected.arity()];
//	for (int i = 0; i < expected.arity(); i++) {
//	    e_subs[i] = expected.sub(i);
//	}
//
//	expected = TB.equals(TB.ife(TB.equals(t, u), o, i), TB.var(pv[1]));
//
//	simplified = simply.simplify(constr, services);
//
//	assertTrue("Expected:" + expected + ", but is:" + simplified,
//		simplified.equals(expected));
//
//    }
//
//    public void testApplyOnAttribute() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	// none-static
//	// {o.a := pv6, t.a:=i} u.a ~~~>(u?=t) i : (u ?= o) pv6 : u.a
//	// now:
//	// {o.a := pv6, t.a:=i} u.a ~~~> if (u=t) (i) (if (u=o) (pv6) (u.a))
//	Term ta = TB.dot(t, pv[5]);
//	Term pv6 = TB.var(pv[6]);
//	Term constr = createUpdateTerm(new Term[] { oa, pv6, ta, i, ua });
//	Term simplified = simply.simplify(constr, TacletForTests.services());
//
//	Term expected = TB.ife(TB.equals(u, t), i, TB.ife(TB.equals(u, o), pv6,
//		ua));
//
//	assertEquals(simplified, expected);
//
//    }
//
//    public void testDeletionStrategy() {
//
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	Services services = TacletForTests.services();
//
//	Term parsed = parseTerm("{t:=i} \\<{}\\> o=o");
//	Term expected = parseTerm("\\<{}\\>o=o");
//	Term result = us.simplify(parsed, services);
//	assertTrue("Expected:" + expected + "\n Is:" + result, result == parsed
//		.sub(parsed.arity() - 1));
//
//	parsed = parseTerm("{t:=i || o:=a}\\<{}\\>t=t");
//	result = us.simplify(parsed, services);
//	expected = parseTerm("{t:=i}\\<{}\\> t=t");
//	assertTrue("Expected: " + expected + "\n Is: " + result, result
//		.equals(expected));
//
//	parsed = parseTerm("{t:=i || o:=a || u:=u}\\<{}\\> t=t");
//	result = us.simplify(parsed, services);
//	expected = parseTerm("{t:=i}\\<{}\\>t=t");
//	assertTrue("Expected: " + expected + "\n Is: " + result, result
//		.equals(expected));
//
//	parsed = parseTerm("{t:=i || o:=a || u:=u}\\<{}\\>u=u");
//	result = us.simplify(parsed, services);
//	expected = parseTerm("\\<{}\\>u=u");
//	assertTrue("Expected: " + expected + "\n Is: " + result, result
//		.equals(expected));
//
//	// {t:=i, o:=a, u:=u}<{ o = o; }> t=t -->
//	// {t:=i, o:=a} <{ o = o; }> t=t
//	parsed = parseTerm("{t:=i || o:=a || u:=u}\\<{ o = o; }\\> t=t");
//	result = us.simplify(parsed, services);
//	expected = parseTerm("{t:=i || o:=a}\\<{ o = o; }\\> t=t");
//
//	assertEquals("Failed deletion of unused var (or simple updates) in "
//		+ "{t:=i || o:=a || u:=u}<{ o = o; }> t=t", expected, result);
//
//	parsed = parseTerm("{t:=i || o:=a || u:=o} \\<{}\\> t=u");
//	result = us.simplify(parsed, services);
//	expected = parseTerm("{t:=i || u:=o}\\<{}\\> t=u");
//	assertEquals("Failed deletion of unused var in "
//		+ "{t:=i || o:=a || u:=o} t=u", expected, result);
//
//    }
//
//    public void testSimultaneousUpdateEquality() {
//	Term cmp1 = parseTerm("{t:=i || o:=a || u:=o} true");
//	Term cmp2 = parseTerm("{o:=a || u:=o || t:=i} true");
//
//	assertTrue("ProgramVariables commute.", cmp1.equals(cmp2));
//    }
//
//    public void testApplicationOnAttributeNoneSim() {
//
//	UpdateSimplifier simply = new UpdateSimplifier();
//
//	Term loc1 = TB.dot(TB.var(pv[4]), pv[5]);
//	Term loc2 = TB.dot(TB.var(pv[3]), pv[5]);
//	Term val = TB.var(pv[2]);
//
//	// {p4.p5 := i} {p3.p5 := i} (p4.p5 = p3.p5)
//
//	Term constr = createUpdateTerm(new Term[] {
//		loc1,
//		val,
//		createUpdateTerm(new Term[] { loc2, val, TB.equals(loc2, loc1) }) });
//	Term simplified = simply.simplify(constr, TacletForTests.services());
//	Term expected = TB.tf().createEqualityTerm(val, val);
//	assertEquals("Error applying non-simultaneous updates on attributes.",
//		expected, simplified);
//    }
//
//    public void testApplicationOnAttributeSim() {
//
//	UpdateSimplifier simply = new UpdateSimplifier();
//
//	Term loc1 = TB.dot(TB.var(pv[4]), pv[5]);
//	Term loc2 = TB.dot(TB.var(pv[3]), pv[5]);
//	Term val = TB.var(pv[2]);
//
//	// {u.a := i} {p3.a := i} (p4.p5 = p3.a)
//
//	Term constr = createUpdateTerm(new Term[] { loc1, val, loc2, val,
//		TB.equals(loc2, loc1) });
//	Term simplified = simply.simplify(constr, TacletForTests.services());
//	Term expected = TB.tf().createEqualityTerm(val, val);
//	assertEquals("Error applying simultaneous update on attributes.",
//		expected, simplified);
//    }
//
//    public void testBugInUStarComputation() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//
//	Term p4p5 = TB.dot(TB.var(pv[4]), pv[5]);
//	Term p1 = TB.var(pv[1]);
//	Term p2 = TB.var(pv[2]);
//
//	// {t:=u.a || u.a := i} {u.a := t} <>(i=i)
//
//	Term constr = createUpdateTerm(new Term[] {
//		p1,
//		p4p5,
//		p4p5,
//		p2,
//		createUpdateTerm(new Term[] {
//			p4p5,
//			p1,
//			TB.dia(JavaBlock.createJavaBlock(new StatementBlock()),
//				TB.equals(p2, p2)) }) });
//	Term simplified = simply.simplify(constr, TacletForTests.services());
//	Term expected = createUpdateTerm(new Term[] {
//		p1,
//		p4p5,
//		p4p5,
//		p4p5,
//		TB.dia(JavaBlock.createJavaBlock(new StatementBlock()), TB
//			.equals(p2, p2)) });
//	assertEquals("Error when merging updates.", expected, simplified);
//    }
//
//    public void xtestBugInDeleteTrivialUpdates() {
//	// deletion of updates has been wrong for the folowing case:
//	// {o1.a:=c || o2.a:=o2.a} phi
//	// previously o2.a:=o2.a has been deleted, but that is wrong, if o1=o2
//
//	UpdateSimplifier simply = new UpdateSimplifier();
//
//	Term p3p5 = TB.dot(TB.var(pv[3]), pv[5]);
//	Term p4p5 = TB.dot(TB.var(pv[4]), pv[5]);
//	Term p1 = TB.var(pv[1]);
//	Term p2 = TB.var(pv[2]);
//
//	// {o.a:=t || u.a := u.a} <>(t=i)
//
//	Term constr = createUpdateTerm(new Term[] {
//		p3p5,
//		p1,
//		p4p5,
//		p4p5,
//		TB.dia(JavaBlock.createJavaBlock(new StatementBlock()), TB
//			.equals(p2, p2)) });
//
//	Term simplified = simply.simplify(constr, TacletForTests.services());
//	Term expected = constr;
//	assertEquals("Trivial updates may only be deleted if it is safe.",
//		expected, simplified);
//    }
//
//    // more systematic tests
//
//    /**
//     * tests the application of
//     * <ul>
//     * <li> {o := t} o </li>
//     * <li> {o := t} u </li>
//     * <li> {o := t} o.a </li>
//     * <li> {o := t} u.a </li>
//     * <li> {o := t} r.a </li>
//     * <li> {a := b} a[i] </li>
//     * <li> {a := b} c[i] </li>
//     * <li> {i := j} a[i] </li>
//     * </ul>
//     */
//    public void testBaseLocalVariableApplications() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	Services services = TacletForTests.services();
//
//	// {o:=t} o
//	Term constr = createUpdateTerm(new Term[] { o, t, o });
//	Term simplified = simply.simplify(constr, services);
//	Term expected = t;
//	assertEquals("Failed applying {o := t} o ", expected, simplified);
//	// {o := t} u
//	constr = createUpdateTerm(new Term[] { o, t, u });
//	simplified = simply.simplify(constr, services);
//	expected = u;
//	assertEquals("Failed applying {o := t} u (o,u compatible) ", expected,
//		simplified);
//
//	// {o := t} r
//	constr = createUpdateTerm(new Term[] { o, t, r });
//	simplified = simply.simplify(constr, services);
//	expected = r;
//	assertEquals("Failed applying {o := t} r (o, r not compatible) ",
//		expected, simplified);
//
//	// {o := t} o.a
//	constr = createUpdateTerm(new Term[] { o, t, oa });
//	simplified = simply.simplify(constr, services);
//	expected = TB.dot(t, pv[5]);
//	assertEquals("Failed applying {o := t} o.a", expected, simplified);
//
//	// {o := t} u.a
//	constr = createUpdateTerm(new Term[] { o, t, ua });
//	simplified = simply.simplify(constr, services);
//	expected = ua;
//	assertEquals("Failed applying {o := t} u.a (o, u compatible) ",
//		expected, simplified);
//	// {o := t} r.a
//	constr = createUpdateTerm(new Term[] { o, t, ra });
//	simplified = simply.simplify(constr, services);
//	expected = ra;
//	assertEquals("Failed applying {o := t} r.a (o, r not compatible) ",
//		expected, simplified);
//
//	// {a := b} a[i]
//	constr = createUpdateTerm(new Term[] { a, b, ai });
//	simplified = simply.simplify(constr, services);
//	expected = bi;
//	assertEquals("Failed applying {a := b} a[i] ", expected, simplified);
//
//	// {a := b} b[i]
//	constr = createUpdateTerm(new Term[] { a, b, ai });
//	simplified = simply.simplify(constr, services);
//	expected = bi;
//	assertEquals("Failed applying {a := b} b[i] (a, b compatible)",
//		expected, simplified);
//
//	// {a := b} c[i]
//	constr = createUpdateTerm(new Term[] { a, b, ci });
//	simplified = simply.simplify(constr, services);
//	expected = ci;
//	assertEquals("Failed applying {a := b} c[i] (a, c not compatible) ",
//		expected, simplified);
//
//	// {i := j} a[i]
//	constr = createUpdateTerm(new Term[] { idx, jdx, ai });
//	simplified = simply.simplify(constr, services);
//	expected = aj;
//	assertEquals("Failed applying {i := j} a[i] (o, r not compatible) ",
//		expected, simplified);
//
//    }
//
//    /**
//     * tests the application of
//     * <ul>
//     * <li> {o.a := t} o.a </li>
//     * <li> {o.a := t} u.a (u compatible to o) </li>
//     * <li> {o.a := t} r.a (r not compatible to o) </li>
//     * <li> {o.a := t} i </li>
//     * <li> {o.a := t} a[i] </li>
//     * </ul>
//     */
//    public void testBaseAttributeApplications() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	Services services = TacletForTests.services();
//
//	// {o.a:=t} o.a
//	Term constr = createUpdateTerm(new Term[] { oa, t, oa });
//	Term simplified = simply.simplify(constr, services);
//	Term expected = t;
//	assertEquals("Failed applying {o.a := t} o.a ", expected, simplified);
//
//	// {o.a:=t} u.a
//	constr = createUpdateTerm(new Term[] { oa, t, ua });
//	simplified = simply.simplify(constr, services);
//	expected = TB.ife(TB.equals(u, o), t, ua);
//	assertEquals("Failed applying {o.a := t} u.a (o, u compatible) ",
//		expected, simplified);
//
//	// {o.a:=t} r.a
//	constr = createUpdateTerm(new Term[] { oa, t, ra });
//	simplified = simply.simplify(constr, services);
//	expected = ra;
//	assertEquals("Failed applying {o.a := t} r.a (o, r not compatible) ",
//		expected, simplified);
//
//	// {o.a:=t} i
//	constr = createUpdateTerm(new Term[] { oa, t, i });
//	simplified = simply.simplify(constr, services);
//	expected = i;
//	assertEquals("Failed applying {o.a := t} i ", expected, simplified);
//
//	// {o.a:=t} a[i]
//	constr = createUpdateTerm(new Term[] { oa, t, ai });
//	simplified = simply.simplify(constr, services);
//	expected = ai;
//	assertEquals("Failed applying {o.a := t} a[i] ", expected, simplified);
//
//	// {o.a:=t} a[i]
//	constr = createUpdateTerm(new Term[] { oa, t, ai });
//	simplified = simply.simplify(constr, services);
//	expected = ai;
//	assertEquals("Failed applying {o.a := t} a[i] ", expected, simplified);
//    }
//
//    /**
//     * tests the application of
//     * <ul>
//     * <li> {a[i] := t} a[i] </li>
//     * <li> {a[i] := t} a[j] </li>
//     * <li> {a[i] := t} b[i] (a compatible to b) </li>
//     * <li> {a[i] := t} b[j] (a compatible to b) </li>
//     * <li> {a[i] := t} c[j] (a not compatible to c) </li>
//     * <li> {a[i] := t} o.a </li>
//     * <li> {a[i] := t} i </li>
//     * </ul>
//     */
//    public void testBaseArrayApplications() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	Services services = TacletForTests.services();
//
//	// {a[i]:=t} a[i]
//	Term constr = createUpdateTerm(new Term[] { ai, t, ai });
//	Term simplified = simply.simplify(constr, services);
//	Term expected = t;
//	assertEquals("Failed applying {a[i] := t} a[i] ", expected, simplified);
//
//	// {a[i]:=t} a[j]
//	constr = createUpdateTerm(new Term[] { ai, t, aj });
//	simplified = simply.simplify(constr, services);
//	expected = TB.ife(TB.equals(jdx, idx), t, aj);
//	assertEquals("Failed applying {a[i] := t} a[j] ", expected, simplified);
//
//	// {a[i]:=t} b[i]
//	constr = createUpdateTerm(new Term[] { ai, t, bi });
//	simplified = simply.simplify(constr, services);
//	expected = TB.ife(TB.equals(b, a), t, bi);
//	assertEquals(
//		"Failed applying {a[i] := t} b[i] " + "(a, b compatible) ",
//		expected, simplified);
//
//	// {a[i]:=t} b[j]
//	constr = createUpdateTerm(new Term[] { ai, t, bj });
//	simplified = simply.simplify(constr, services);
//	expected = TB.ife(TB.and(TB.equals(b, a), TB.equals(jdx, idx)), t, bj);
//	assertEquals(
//		"Failed applying {a[i] := t} b[j] " + "(a, b compatible) ",
//		expected, simplified);
//
//	// {a[i]:=t} c[j]
//	constr = createUpdateTerm(new Term[] { ai, t, cj });
//	simplified = simply.simplify(constr, services);
//	expected = cj;
//	assertEquals("Failed applying {a[i] := t} c[j] "
//		+ "(a, c not compatible) ", expected, simplified);
//
//	// {a[i]:=t} o.a
//	constr = createUpdateTerm(new Term[] { ai, t, oa });
//	simplified = simply.simplify(constr, services);
//	expected = oa;
//	assertEquals("Failed applying {a[i] := t} o.a ", expected, simplified);
//
//	// {a[i]:=t} t
//	constr = createUpdateTerm(new Term[] { ai, t, t });
//	simplified = simply.simplify(constr, services);
//	expected = t;
//	assertEquals("Failed applying {a[i] := t} t ", expected, simplified);
//
//	// {a[i]:=t} a
//	constr = createUpdateTerm(new Term[] { ai, t, a });
//	simplified = simply.simplify(constr, services);
//	expected = a;
//	assertEquals("Failed applying {a[i] := t} a ", expected, simplified);
//    }
//
//    /**
//     * tests the application of
//     * <ul>
//     * <li> {a := b} {a[i] := o} <> true </li>
//     * <li> {i := j} {a[i] := o} <> true </li>
//     * <li> {a[i] := t} {a[i] := o} <> true </li>
//     * <li> {a[i] := t} {b[i] := o} <> true (a, b compatible) </li>
//     * <li> {a[i] := t} {c[i] := o} <> true (a, c not compatible)</li>
//     * <li> {a[i] := t} {o := a[i]} <> true </li>
//     * <li> {a[i] := t} {o := a[j]} <> true </li>
//     * <li> {o.a := t} {o.a := o } <> true </li>
//     * <li> {o.a := t} {o.a.a := o} <> true </li>
//     * <li> {o.a := t} {o.a.a := o.a} <> true </li>
//     * <li> {o.a := t} {u.a := u.a} <> true </li>
//     * <li> {o.a := t} {r.a := r.a} <> true </li>
//     * <li> {o.a := t} {r.a.a := o} <> true </li>
//     * </ul>
//     */
//    public void testMergeSingleUpdates() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	Services services = TacletForTests.services();
//	Term diaTrue = TB.dia(JavaBlock.createJavaBlock(new StatementBlock()),
//		TB.tt());
//
//	// {a := b} {a[i] := o} <> true
//	Term constr = createUpdateTerm(new Term[] { a, b,
//		createUpdateTerm(new Term[] { ai, o, diaTrue }) });
//	Term simplified = simply.simplify(constr, services);
//	Term expected = createUpdateTerm(new Term[] { a, b, bi, o, diaTrue });
//
//	assertEquals("Failed applying {a := b} {a[i] := o} <> true", expected,
//		simplified);
//
//	// {i := j} {a[i] := o} <> true
//	constr = createUpdateTerm(new Term[] { idx, jdx,
//		createUpdateTerm(new Term[] { ai, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { idx, jdx, aj, o, diaTrue });
//
//	assertEquals("Failed applying {i := j} {a[i] := o} <> true", expected,
//		simplified);
//
//	// {a[i] := t} {a[i] := o} <> true
//	constr = createUpdateTerm(new Term[] { ai, t,
//		createUpdateTerm(new Term[] { ai, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { ai, o, diaTrue });
//
//	assertEquals("Failed applying {i := j} {a[i] := o} <> true", expected,
//		simplified);
//
//	// {a[i] := t} {b[i] := o} <> true (a, b compatible)
//	constr = createUpdateTerm(new Term[] { ai, t,
//		createUpdateTerm(new Term[] { bi, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	/*
//	 * expected = createUpdateTerm (new Term[]{ai, tf.createConjCondTerm(new
//	 * Term[]{a, idx, t, b, idx, ai}), bi, o, diaTrue});
//	 */// skipped this kind of improvement
//	expected = createUpdateTerm(new Term[] { ai, t, bi, o, diaTrue });
//
//	assertEquals("Failed applying {a[i] := t} {b[i] := o} <> true"
//		+ "(a,b compatible)", expected, simplified);
//
//	// {a[i] := t} {c[i] := o} <> true (a, c not compatible)
//	constr = createUpdateTerm(new Term[] { ai, t,
//		createUpdateTerm(new Term[] { ci, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { ai, t, ci, o, diaTrue });
//	assertEquals("Failed applying {a[i] := t} {c[i] := o} <> true"
//		+ "(a, c not compatible)", expected, simplified);
//
//	// {a[i] := t} {o := a[i]} <> true
//	constr = createUpdateTerm(new Term[] { ai, t,
//		createUpdateTerm(new Term[] { o, ai, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { ai, t, o, t, diaTrue });
//
//	assertEquals("Failed applying {a[i] := t} {o:=a[i]} <> true", expected,
//		simplified);
//
//	// {a[i] := t} {o := a[j]} <> true
//	constr = createUpdateTerm(new Term[] { ai, t,
//		createUpdateTerm(new Term[] { o, aj, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { ai, t, o,
//		TB.ife(TB.equals(jdx, idx), t, aj), diaTrue });
//	assertEquals("Failed applying {a[i] := t} {o:=a[j]} <> true", expected,
//		simplified);
//
//	// {o.a := t} {o.a := o} <> true
//	constr = createUpdateTerm(new Term[] { oa, t,
//		createUpdateTerm(new Term[] { oa, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { oa, o, diaTrue });
//	assertEquals("Failed applying  {o.a := t} {o.a := o}<> true", expected,
//		simplified);
//
//	// {o.a := t} {o.a.a := o} <> true
//	Term oaa = TB.dot(oa, pv[5]);
//	Term ta = TB.dot(t, pv[5]);
//	constr = createUpdateTerm(new Term[] { oa, t,
//		createUpdateTerm(new Term[] { oaa, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	/*
//	 * expected = createUpdateTerm (new Term[]{oa,
//	 * tf.createIfElseTerm(o,t,oa, t), ta, o, diaTrue});
//	 */// skipped this improvement
//	expected = createUpdateTerm(new Term[] { oa, t, ta, o, diaTrue });
//	assertEquals("Failed applying {o.a := t} {o.a.a := o}<> true ",
//		expected, simplified);
//
//	// {o.a := t} {o.a.a := o.a} <> true
//	constr = createUpdateTerm(new Term[] { oa, t,
//		createUpdateTerm(new Term[] { oaa, oa, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	/*
//	 * expected = createUpdateTerm (new Term[]{oa,
//	 * tf.createIfElseTerm(o,t,oa, t), ta, t, diaTrue});
//	 */// this "optimization" is no longer performed
//	expected = createUpdateTerm(new Term[] { oa, t, ta, t, diaTrue });
//	assertEquals("Failed applying {o.a := t} {o.a.a := o.a} <> true",
//		expected, simplified);
//	// {o.a := t} {u.a := u.a} <> true
//	constr = createUpdateTerm(new Term[] { oa, t,
//		createUpdateTerm(new Term[] { ua, ua, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	/*
//	 * expected = createUpdateTerm (new Term[] { oa, tf.createIfElseTerm
//	 * (o,u,oa,t), ua, tf.createIfElseTerm (u,o,t,ua), diaTrue });
//	 */
//	expected = createUpdateTerm(new Term[] { oa, t, diaTrue });
//	assertEquals("Failed applying {o.a := t} {u.a := u.a} <> true"
//		+ "(o, u compatible)", expected, simplified);
//
//	// {o.a := t} {r.a := r.a} <> true
//	constr = createUpdateTerm(new Term[] { oa, t,
//		createUpdateTerm(new Term[] { ra, ra, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	expected = createUpdateTerm(new Term[] { oa, t, diaTrue });
//	assertEquals("Failed applying {o.a := t} {r.a := r.a} <> true"
//		+ "(o, r bot compatible)", expected, simplified);
//
//	// {o.a := t} {r.a.a := o} <> true
//	Term raa = TB.dot(ra, pv[5]);
//	constr = createUpdateTerm(new Term[] { oa, t,
//		createUpdateTerm(new Term[] { raa, o, diaTrue }) });
//	simplified = simply.simplify(constr, services);
//	/*
//	 * expected = createUpdateTerm (new Term[] { oa, tf.createIfElseTerm(o,
//	 * ra, oa, t), raa, o, diaTrue });
//	 */// this "optimisation" is no longer performed
//	expected = createUpdateTerm(new Term[] { oa, t, raa, o, diaTrue });
//	assertEquals("Failed applying {o.a := t} {r.a.a := o} <> true"
//		+ "(o, r not compatible)", expected, simplified);
//
//    }
//
//    /**
//     * tests the application of
//     * <ul>
//     * <li> {o.spv:=u, t.spv:=i} u.spv </li>
//     * </ul>
//     */
//    public void testStaticAttributes() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	// {o.spv:=u, t.spv:=i} u.spv ~~~> i
//	Term tspv = TB.dot(t, spv);
//	Term constr = createUpdateTerm(new Term[] { ospv, u, tspv, i, uspv });
//	Term simplified = simply.simplify(constr, TacletForTests.services());
//	Term expected = i;
//	assertSame("Failed applying {o.spv:=pv6, t.spv:=i} u.spv", expected,
//		simplified);
//    }
//
//    /**
//     * tests the application of
//     * <ul>
//     * <li> {a[i] := t, a[j] :=u} a[i] </li>
//     * <li> {a[j] := t, a[i] :=u} a[i] </li>
//     * <li> {a[j] := t, a[i] := o, a[m] := u} a[i] </li>
//     * <li> {a[i] := u, a[m] := u} a[i] </li>
//     * </ul>
//     */
//    public void testSimultaneousArrayApplications() {
//	UpdateSimplifier simply = new UpdateSimplifier();
//	Services services = TacletForTests.services();
//
//	// {a[i] := t, a[j] :=u} a[i]
//	Term constr = createUpdateTerm(new Term[] { ai, t, aj, u, ai });
//	Term simplified = simply.simplify(constr, services);
//	Term expected = TB.ife(TB.equals(idx, jdx), u, t);
//	assertEquals("Failed applying {a[i] := t, a[j] :=u} a[i]", expected,
//		simplified);
//
//	// {a[j] := t, a[i] := u} a[i]
//	constr = createUpdateTerm(new Term[] { aj, t, ai, u, ai });
//	simplified = simply.simplify(constr, services);
//	expected = u;
//	assertEquals("Failed applying {a[j] := t, a[i] := u} a[i]", expected,
//		simplified);
//
//	// {a[j] := t, a[m] := u} a[i]
//	constr = createUpdateTerm(new Term[] { aj, t, am, u, ai });
//	simplified = simply.simplify(constr, services);
//	expected = TB.ife(TB.equals(idx, mdx), u, TB.ife(TB.equals(idx, jdx),
//		t, ai));
//	assertEquals("Failed applying {a[j] := t, a[m] := u} a[i]", expected,
//		simplified);
//
//	// {a[I] := u, a[m] := u} a[i]
//	// important to check simplification of conj cond
//	constr = createUpdateTerm(new Term[] { ai, u, am, u, ai });
//	simplified = simply.simplify(constr, services);
//	expected = u;
//	assertEquals("Failed applying {a[i] := u, a[m] := u} a[i]", expected,
//		simplified);
//
//    }
//
//    /**
//     * tests the application of updates on more complex terms. In particular it
//     * is tested if conditional terms are simplified as far as possible.
//     * <ul>
//     * <li> {a[i] := u, c[j] :=u} (a * j : a[i] ?= b * m : c[j]) </li>
//     * <li> {a[i] := u, c[j] :=u} (a * j : a[i] ?= b * m : c[j]) </li>
//     * <li> {i := j} (a * j : a[i] ?= a * i : c[j]) </li>
//     * <li> {o.a := u, r.a :=u} (o ?= u) o.a : r.a </li>
//     * <li> {o := u} (o ?= u) u.a : o.a </li>
//     * </ul>
//     */
//    // public void testSimultaneousUpdateApplicationOnComposedTerms() {
//    // UpdateSimplifier simply=new UpdateSimplifier();
//    //
//    //	
//    // Term constr = createUpdateTerm(new Term[]
//    // {ai, u, cj, u, tf.createConjCondTerm
//    // (new Term[]{a, jdx, ai, b, mdx, cj})});
//    // Term simplified = simply.simplify(constr);
//    // Term expected = u;
//    // assertEquals("Failed applying {a[i] := u, c[j] :=u}" +
//    // "(a * j : a[i] ?= b * m : c[j]) ",
//    // expected, simplified);
//    //
//    // // {a[i] := u, c[j] :=t} (a * j : a[i] ?= b * m : c[j])
//    // constr = createUpdateTerm(new Term[]
//    // {ai, u, cj, t, tf.createConjCondTerm
//    // (new Term[]{a, jdx, ai, b, mdx, cj})});
//    // simplified = simply.simplify(constr);
//    // expected = tf.createConjCondTerm
//    // (new Term[]{a, jdx, u, b, mdx, t});
//    // assertEquals("Failed applying {a[i] := u, c[j] :=t}" +
//    // "(a * j : a[i] ?= b * m : c[j]) ",
//    // expected, simplified);
//    //
//    // // {i := j} (a * j : a[i] ?= a * i : c[j])
//    // constr = createUpdateTerm(new Term[]
//    // {idx, jdx, tf.createConjCondTerm
//    // (new Term[]{a, jdx, ai, a, jdx, cj})});
//    // simplified = simply.simplify(constr);
//    // expected = cj;
//    // assertSame("Failed applying {i := j} (a * j : a[i] ?= a * i : c[j]) ",
//    // expected, simplified);
//    //
//    // // {o.a := u, r.a :=u} (o ?= u) o.a : r.a
//    // constr = createUpdateTerm(new Term[]
//    // {oa, u, ra, u, tf.createIfElseTerm
//    // (o, u, oa, ra)});
//    // simplified = simply.simplify(constr);
//    // expected = u;
//    // assertSame("Failed applying {o.a := u, r.a :=u} (o ?= u) o.a : r.a ",
//    // expected, simplified);
//    // // {o := u} (o ?= u) u.a : o.a
//    // constr = createUpdateTerm(new Term[]
//    // {o, u, tf.createIfElseTerm
//    // (o, u, ua, oa)});
//    // simplified = simply.simplify(constr);
//    // expected = ua;
//    // assertSame("Failed applying {o := u} (o ?= u) u.a : o.a ",
//    // expected, simplified);
//    //
//    // // {o := t} (o ?= u) u.a : o.a
//    // Term ta = tf.dot(pv[5], t);
//    // constr = createUpdateTerm(new Term[]
//    // {o, t, tf.createIfElseTerm
//    // (o, u, ua, oa)});
//    // simplified = simply.simplify(constr);
//    // expected = tf.createIfElseTerm(t, u, ua, ta);
//    // assertEquals("Failed applying {o := t} (o ?= u) u.a : o.a ",
//    // expected, simplified);
//    //
//    //
//    // // {r := t} (o ?= u) u.a : o.a
//    // constr = createUpdateTerm(new Term[]
//    // {r, t, tf.createIfElseTerm(o, u, ua, oa)});
//    // simplified = simply.simplify(constr);
//    // expected = constr.sub(1);
//    // assertSame("Failed applying {r := t} (o ?= u) u.a : o.a " +
//    // "(r incompatible to o,u", expected, simplified);
//    //	
//    // }
//    // new testing style here
//    private final HelperClassForTests helper = new HelperClassForTests();
//
//    public static final String testRules = System.getProperty("key.home")
//	    + File.separator + "examples" + File.separator + "_testcase"
//	    + File.separator + "updatesimplification";
//
//    public void testAttributeEvaluateSubsFirst() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testAttributeRule1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier();
//	assertEquals("Evaluate attribute references under the update first", t1
//		.sub(1), us.simplify(t1.sub(0), proofList.getFirstProof()
//		.getServices()));
//    }
//
//    public void testAttributeRule3() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testAttributeRule3.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier();
//	assertEquals(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//    }
//
//    public void testAttributeRule4() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testAttributeRule4.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier();
//	assertEquals(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//    }
//
//    public void testShadowedArraySimplificationRule() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testShadowedArrayRule1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier();
//	assertEquals("Shadowed array are not aliased to "
//		+ "their unshadowed version", t1.sub(1), us.simplify(t1.sub(0),
//		proofList.getFirstProof().getServices()));
//    }
//
//    public void testApplyArrayAccessOnShadowedArray() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testShadowedArrayRule2.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("An array is aliased to " + "its shadowed version", t1
//		.sub(1), us.simplify(t1.sub(0), proofList.getFirstProof()
//		.getServices()));
//    }
//
//    public void testApplyShadowedAttributeOnAttribute() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testShadowedAttributeRule1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier();
//	assertEquals("Shadowed attributes are not aliased to "
//		+ "their unshadowed version", t1.sub(1), us.simplify(t1.sub(0),
//		proofList.getFirstProof().getServices()));
//    }
//
//    public void testApplyAttributeOnShadowedAttribute() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testShadowedAttributeRule2.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("An attribute is aliased to " + "its shadowed version", t1
//		.sub(1), us.simplify(t1.sub(0), proofList.getFirstProof()
//		.getServices()));
//    }
//
//    public void testShadowOnShadowSameTransactionNr() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testShadowOnShadowSameNr.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Same number means shadows are aliased.", t1.sub(1), us
//		.simplify(t1.sub(0), proofList.getFirstProof().getServices()));
//    }
//
//    public void testDeletion() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Deletion is broken.", t1.sub(1), us.simplify(t1.sub(0),
//		proofList.getFirstProof().getServices()));
//    }
//
//    public void testNoDeletionIfAppliedOnNonRigidFunction() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion2.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Deletion is broken.", t1.sub(1), us.simplify(t1.sub(0),
//		proofList.getFirstProof().getServices()));
//    }
//
//    public void testDeletion3() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion3.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//	assertEquals(Update.createUpdate(t1.sub(1)).getAllAssignmentPairs()
//		.size(), 2);
//    }
//
//    public void testDeletion4() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion4.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//	assertEquals(Update.createUpdate(t1.sub(1)).getAllAssignmentPairs()
//		.size(), 1);
//    }
//
//    public void testDeletion5() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion5.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//	assertEquals(Update.createUpdate(t1.sub(1)).getAllAssignmentPairs()
//		.size(), 1);
//    }
//
//    public void testDeletion6() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion6.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//	assertEquals(Update.createUpdate(t1.sub(1)).getAllAssignmentPairs()
//		.size(), 1);
//    }
//
//    public void testDeletion7() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion7.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1, us.simplify(t1, proofList.getFirstProof()
//		.getServices()));
//	assertEquals(Update.createUpdate(t1).getAllAssignmentPairs().size(), 2);
//    }
//
//    public void testDeletion8() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion8.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1, us.simplify(t1, proofList.getFirstProof()
//		.getServices()));
//	assertEquals(Update.createUpdate(t1).getAllAssignmentPairs().size(), 2);
//    }
//
//    public void testDeletion9() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion9.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//	assertEquals(Update.createUpdate(t1.sub(1)).getAllAssignmentPairs()
//		.size(), 2);
//    }
//
//    public void testDeletion10() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion10.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1.sub(1), us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()));
//	assertEquals(Update.createUpdate(t1.sub(1)).getAllAssignmentPairs()
//		.size(), 2);
//    }
//
//    public void testDeletion11() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testDeletion11.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(t1, us.simplify(t1, proofList.getFirstProof()
//		.getServices()));
//	assertEquals(Update.createUpdate(t1).getAllAssignmentPairs().size(), 3);
//    }
//
//    public void testDeletion12() {
//	final Services services = TacletForTests.services();
//
//	final UpdateFactory uf = new UpdateFactory(services,
//		new UpdateSimplifier(true, false));
//
//	final Term zeroAccess = TB.array(services, TB.var(arrayVar1), TB.zTerm(
//		services, "0"));
//	final Term intVarAccess = TB.array(services, TB.var(arrayVar1), TB
//		.var(intVar));
//
//	final Update parUpd = uf.parallel(uf.quantify(arrayVar1, uf
//		.elementaryUpdate(zeroAccess, o)), uf.quantify(intVar, uf
//		.elementaryUpdate(intVarAccess, u)));
//
//	assertEquals(parUpd.getAllAssignmentPairs().size(), 2);
//	assertSame(parUpd.getAssignmentPair(0).boundVars()
//		.lastQuantifiableVariable(), arrayVar1);
//	assertSame(parUpd.getAssignmentPair(1).boundVars()
//		.lastQuantifiableVariable(), intVar);
//
//	final Term updateTerm = uf.apply(parUpd, TB.dia(JavaBlock
//		.createJavaBlock(new StatementBlock()), TB.equals(o, o)));
//
//	assertEquals(Update.createUpdate(updateTerm).getAllAssignmentPairs()
//		.size(), 2);
//    }
//
//    public void testAnonymous1() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testAnonymous1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Anonymous updates are broken.", t1.sub(1), us.simplify(t1
//		.sub(0), proofList.getFirstProof().getServices()));
//    }
//
//    public void testAnonymous2() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testAnonymous2.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Anonymous updates are broken.", t1.sub(1), us.simplify(t1
//		.sub(0), proofList.getFirstProof().getServices()));
//    }
//
//    public void testHeapDependentFunctions1() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testHeapDependent1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Update simplification rule for heap dependent "
//		+ "function symbols broken.", t1.sub(1), us.simplify(t1.sub(0),
//		proofList.getFirstProof().getServices()));
//    }
//
//    public void testHeapDependentFunctions2() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testHeapDependent1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEquals("Update simplification rule for heap dependent "
//		+ "function symbols broken.", t1.sub(1), us.simplify(t1.sub(0),
//		proofList.getFirstProof().getServices()));
//    }
//
//    public void testQuantified1() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testQuantified1.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()), t1.sub(1));
//    }
//
//    public void testQuantified2() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testQuantified2.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()), t1.sub(1));
//    }
//
//    public void testQuantified3() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testQuantified3.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()), t1.sub(1));
//    }
//
//    public void testQuantified4() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testQuantified4.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()), t1.sub(1));
//    }
//
//    public void testQuantified5() {
//	ProofAggregate proofList = helper.parse(new File(testRules
//		+ File.separator + "testQuantified5.key"));
//	Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	UpdateSimplifier us = new UpdateSimplifier(true, false);
//	assertEqualsModRenaming(us.simplify(t1.sub(0), proofList
//		.getFirstProof().getServices()), t1.sub(1));
//    }
//
//    public void testLocationFunction() {
//	for (int i = 1; i < 4; i++) {
//	    ProofAggregate proofList = helper.parse(new File(testRules
//		    + File.separator + "testLocationFunction" + i + ".key"));
//	    Term t1 = helper.extractProblemTerm(proofList.getFirstProof());
//	    UpdateSimplifier us = new UpdateSimplifier(true, false);
//	    assertEqualsModRenaming(us.simplify(t1.sub(0), proofList
//		    .getFirstProof().getServices()), t1.sub(1));
//	}
//    }
//
//    public static void main(String[] args) {
//	TestUpdateSimplifier tsus = new TestUpdateSimplifier("t");
//	tsus.setUp();
//	tsus.testDeletion();
//	// tsus.testBasicRules();
//	// tsus.testDeletionStrategy();
//	// tsus.testSimultaneousUpdateEquality();
//	// tsus.testApplyOnAttribute();
//    }
}
