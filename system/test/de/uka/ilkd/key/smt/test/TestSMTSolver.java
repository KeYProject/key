// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.

package de.uka.ilkd.key.smt.test;

import java.io.File;

import junit.framework.Assert;

public abstract class TestSMTSolver extends TestCommons {
	public static final String testFile = System.getProperty("key.home")
	        + File.separator + "examples" + File.separator + "_testcase"
	        + File.separator + "smt" + File.separator;

	protected void setUp() {
	}

	@Override
	protected void tearDown() throws Exception {
	}

	public void testAndnot() {
		Assert.assertTrue(correctResult(testFile + "andnot.key", false));
	}

	public void testOrnot() {
		Assert.assertTrue(correctResult(testFile + "ornot.key", true));
	}

	public void testAndornot() {
		Assert.assertTrue(correctResult(testFile + "andornot.key", false));
	}

	public void testAndornot2() {
		Assert.assertTrue(correctResult(testFile + "andornot2.key", true));
	}

	public void testImply() {
		Assert.assertTrue(correctResult(testFile + "imply.key", true));
	}

	public void testImply2() {
		Assert.assertTrue(correctResult(testFile + "imply2.key", true));
	}

	public void testImply3() {
		Assert.assertTrue(correctResult(testFile + "imply3.key", false));
	}

	public void testEqui1() {
		Assert.assertTrue(correctResult(testFile + "equi1.key", true));
	}

	public void testEqui2() {
		Assert.assertTrue(correctResult(testFile + "equi2.key", false));
	}

	public void testAllex1() {
		Assert.assertTrue(correctResult(testFile + "allex1.key", true));
	}

	public void testAllex2() {
		Assert.assertTrue(correctResult(testFile + "allex2.key", false));
	}

	public void testAllex3() {
		Assert.assertTrue(correctResult(testFile + "allex3.key", true));
	}

	public void testLogicalIte1() {
		Assert.assertTrue(correctResult(testFile + "logicalite1.key", true));
	}

	public void testLogicalIte2() {
		Assert.assertTrue(correctResult(testFile + "logicalite2.key", false));
	}

	public void testTermIte1() {
		if (getSolverType().supportsIfThenElse())
			Assert.assertTrue(correctResult(testFile + "termite1.key", true));
	}

	public void testTermlIte2() {
		if (getSolverType().supportsIfThenElse())
			Assert.assertTrue(correctResult(testFile + "termite2.key", false));
	}

	public void testEqual1() {
		Assert.assertTrue(correctResult(testFile + "equal1.key", true));
	}

	public void testEqual2() {
		Assert.assertTrue(correctResult(testFile + "equal2.key", false));
	}

	public void testSubsort1() {
		Assert.assertTrue(correctResult(testFile + "subsort1.key", true));
	}

	public void testSubsort2() {
		Assert.assertTrue(correctResult(testFile + "subsort2.key", false));
	}

	public void testAdd1() {
		Assert.assertTrue(correctResult(testFile + "add1.key", true));
	}

	public void testBSum1() {
		Assert.assertTrue(correctResult(testFile + "bsum1.key", true));
	}

	public void testBSum2() {
		Assert.assertTrue(correctResult(testFile + "bsum2.key", true));
	}

	public void testBSum3() {
		Assert.assertTrue(correctResult(testFile + "bsum3.key", false));
	}

	public void testBProd1() {
		Assert.assertTrue(correctResult(testFile + "bprod1.key", true));
	}

	public void testBProd2() {
		Assert.assertTrue(correctResult(testFile + "bprod2.key", true));
	}

	public void testBProd3() {
		Assert.assertTrue(correctResult(testFile + "bprod3.key", false));
	}

	// public void testBinderPred1() {
	// Assert.assertTrue(correctResult(testFile + "binder2.key", true));
	// }
	public void testBinderPred2() {
		Assert.assertTrue(correctResult(testFile + "binder4.key", true));
	}

	public void testBinderPred3() {
		Assert.assertTrue(correctResult(testFile + "binder5.key", true));
	}
	/*
	 * public void testAdd2() { Assert.assertTrue(correctResult(testFile +
	 * "add2.key", false)); }
	 */
	// not linear, so yices throws exception
	/*
	 * public void testMult1() { Assert.assertTrue(correctResult(testFile +
	 * "mult1.key", true)); }
	 */
}