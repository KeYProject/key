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

import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.File;

public abstract class TestSMTSolver extends TestCommons {
	public static final String testFile = HelperClassForTests.TESTCASE_DIRECTORY
	        + File.separator + "smt" + File.separator;

	@BeforeEach
	public void setUp() {
	}

	@AfterEach
	public void tearDown() throws Exception {
	}

	@Test
	public void testAndnot() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "andnot.key", false));
	}

	@Test
	public void testOrnot() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "ornot.key", true));
	}

	@Test
	public void testAndornot() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "andornot.key", false));
	}

	@Test
	public void testAndornot2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "andornot2.key", true));
	}

	@Test
	public void testImply() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "imply.key", true));
	}

	@Test
	public void testImply2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "imply2.key", true));
	}

	@Test
	public void testImply3() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "imply3.key", false));
	}

	@Test
	public void testEqui1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "equi1.key", true));
	}

	@Test
	public void testEqui2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "equi2.key", false));
	}

	@Test
	public void testAllex1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "allex1.key", true));
	}

	// LONG runtime with CVC3 (~300s)
	@Test
	public void testAllex2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "allex2.key", false));
	}

	@Test
	public void testAllex3() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "allex3.key", true));
	}

	@Test
	public void testLogicalIte1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "logicalite1.key", true));
	}

	@Test
	public void testLogicalIte2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "logicalite2.key", false));
	}

	@Test
	public void testTermIte1() throws Exception {
		if (getSolverType().supportsIfThenElse())
			Assertions.assertTrue(correctResult(testFile + "termite1.key", true));
	}

	// LONG runtime in CVC3 (~300s)
	@Test
	public void testTermlIte2() throws Exception {
		if (getSolverType().supportsIfThenElse())
			Assertions.assertTrue(correctResult(testFile + "termite2.key", false));
	}

	@Test
	public void testEqual1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "equal1.key", true));
	}

	@Test
	public void testEqual2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "equal2.key", false));
	}

	@Test
	public void testSubsort1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "subsort1.key", true));
	}

	@Test
	public void testSubsort2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "subsort2.key", false));
	}

	@Test
	public void testAdd1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "add1.key", true));
	}

	@Test
	public void testBSum1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "bsum1.key", true));
	}

	@Test
	public void testBSum2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "bsum2.key", true));
	}

	@Test
	public void testBSum3() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "bsum3.key", false));
	}

	@Test
	public void testBProd1() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "bprod1.key", true));
	}

	@Test
	public void testBProd2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "bprod2.key", true));
	}

	@Test
	public void testBProd3() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "bprod3.key", false));
	}

	@Test
	public void testBinderPred2() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "binder4.key", true));
	}

	@Test
	public void testBinderPred3() throws Exception {
		Assertions.assertTrue(correctResult(testFile + "binder5.key", true));
	}
}