// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import junit.framework.TestCase;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.unittest.testing.TestHelper;

public class TestTestGenerator extends TestCase {

    private JavaInfo javaInfo;

    private Profile old;

    public TestTestGenerator(String name) {
	super(name);
    }

    public void setUp() {
	old = ProofSettings.DEFAULT_SETTINGS.getProfile();
	ProofSettings.DEFAULT_SETTINGS.setProfile(TacletForTests.profile);
	TacletForTests.lastFile = null;
	TacletForTests.parse();
	javaInfo = TacletForTests.getJavaInfo();
    }

    public void tearDown() {
	ProofSettings.DEFAULT_SETTINGS.setProfile(old);
	TacletForTests.lastFile = null;
	TacletForTests.parse();
    }

    public void testJUnitClassesAvailable() {
	KeYJavaType testCase = javaInfo
		.getKeYJavaTypeByClassName("junit.framework.TestCase");
	KeYJavaType testSuite = javaInfo
		.getKeYJavaTypeByClassName("junit.framework.TestSuite");
	KeYJavaType stringBuffer = javaInfo
		.getKeYJavaTypeByClassName("java.lang.StringBuffer");
	assertTrue(testCase != null && testSuite != null
		&& stringBuffer != null);
    }

    public void testAbsMin() {
	final TestHelper absMin = new TestHelper("absMin.key",
		TestHelper.ABS_MIN_NAME, true);
	assertTrue(
		"\nTestCase failed because "
			+ absMin.getFName()
			+ " could not be loaded."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		absMin.getProof() != null);

	int is = absMin.getNrofOG();
	int sb = 4;
	assertTrue(
		"\nTestCase failed because "
			+ absMin.getFName()
			+ " has "
			+ is
			+ "Open Goals instead of "
			+ sb
			+ "."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		is == sb);

	is = absMin.nrOfMeth();
	sb = 1;
	assertTrue("\nNr of methods of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	final String isS = absMin.methNames();
	final String sbS = "AbsMin::absMin";
	assertTrue("Name of available methods of " + absMin.getFName() + " is "
		+ isS + " instead of " + sbS + ".", sbS.equals(isS));

	is = absMin.getNrOfNodes();
	sb = 4;
	assertTrue("\nNr of nodes of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	is = absMin.getNrOfStatements();
	sb = 4;
	assertTrue("\nNr of Statements of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	is = absMin.getNrOfMGS();
	sb = 4;
	assertTrue("\nNr of ModelGenerators of " + absMin.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);

	assertTrue("\nOracle of " + absMin.getFName() + " is null", absMin
		.isOracleNnull());

	is = absMin.getNrOfPV();
	sb = 6;
	assertTrue("\nNr of ProgramVariables of " + absMin.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);

	is = absMin.getNrOfPV2();
	sb = 6;
	assertTrue("\nNr of ProgramVariables in TestGenerator of "
		+ absMin.getFName() + " is " + is + " instead of " + sb + ".",
		is == sb);

	is = absMin.getNrOfTestDat();
	sb = 4;
	assertTrue("\nNr of Test Tuples of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	assertTrue(absMin.wrongData(), absMin.checkTestData());
    }

    public void testBrLoopData() {
	TestHelper brLoop = new TestHelper("branchingLoop.proof",
		TestHelper.BRANCHING_LOOP_NAME, false);
	assertTrue(
		"\nTestCase failed because "
			+ brLoop.getFName()
			+ " could not be loaded."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		brLoop.getProof() != null);

	int is = brLoop.getNrofOG();
	int sb = 2;
	assertTrue(
		"\nTestCase failed because "
			+ brLoop.getFName() + " has " + is + "Open Goals instead of " + sb + "."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		is == sb);

	is = brLoop.nrOfMeth();
	sb = 2;
	assertTrue("\nNr of methods of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	final String isS = brLoop.methNames();
	final String sbS = "BranchingLoop::fooBranchingLoop::doIt";
	assertTrue("Name of available methods of " + brLoop.getFName() + " is "
		+ isS + " instead of " + sbS + ".", sbS.equals(isS));

	is = brLoop.getNrOfNodes();
	sb = 6;
	assertTrue("\nNr of nodes of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	is = brLoop.getNrOfStatements();
	sb = 3;
	assertTrue("\nNr of Statements of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	is = brLoop.getNrOfMGS();
	sb = 5;
	assertTrue("\nNr of ModelGenerators of " + brLoop.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);

	assertTrue("\nOracle of " + brLoop.getFName() + " is null", brLoop
		.isOracleNnull());

	is = brLoop.getNrOfPV();
	sb = 4;
	assertTrue("\nNr of ProgramVariables of " + brLoop.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);

	is = brLoop.getNrOfPV2();
	sb = 8;
	assertTrue("\nNr of ProgramVariables in TestGenerator of "
		+ brLoop.getFName() + " is " + is + " instead of " + sb + ".",
		is == sb);

	is = brLoop.getNrOfTestDat();
	sb = 4;
	assertTrue("\nNr of Test Tuples of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

	assertTrue(brLoop.wrongData(), brLoop.checkTestData());
    }

}
