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

    private static TestHelper absMin = null;

    private static TestHelper brLoop = null;

    private JavaInfo javaInfo;

    private Profile old;

    public TestTestGenerator(String name) {
	super(name);
	if (absMin == null) {
	    absMin = new TestHelper("absMin.key", TestHelper.ABS_MIN_NAME, true);
	}
	if (brLoop == null) {
	    brLoop = new TestHelper("branchingLoop.proof",
		    TestHelper.BRANCHING_LOOP_NAME, false);
	}
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

    public void testAbsMinLoad() {
	assertTrue(
		"\nTestCase failed because "
			+ absMin.getFName()
			+ " could not be loaded."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		absMin.getProof() != null);
    }

    public void testBrLoopLoad() {
	assertTrue(
		"\nTestCase failed because "
			+ brLoop.getFName()
			+ " could not be loaded."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		brLoop.getProof() != null);
    }

    public void testAbsMinNrOfGoals() {
	final int is = absMin.getNrofOG();
	final int sb = 4;
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
    }

    public void testBrLoopNrOfGoals() {
	final int is = brLoop.getNrofOG();
	final int sb = 4;
	assertTrue(
		"\nTestCase failed because "
			+ brLoop.getFName()
			+ " has "
			+ is
			+ "Open Goals instead of "
			+ sb
			+ "."
			+ "\nThis is not a poblem with TestGeneration but with something else.",
		is == sb);
    }

    public void testAbsMinNrOfMeth() {
	final int is = absMin.nrOfMeth();
	final int sb = 1;
	assertTrue("\nNr of methods of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

    }

    public void testBrLoopNrOfMeth() {
	final int is = brLoop.nrOfMeth();
	final int sb = 2;
	assertTrue("\nNr of methods of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);

    }

    public void testAbsMinMethNames() {
	final String is = absMin.methNames();
	final String sb = "AbsMin::absMin";
	assertTrue("Name of available methods of " + absMin.getFName() + " is "
		+ is + " instead of " + sb + ".", sb.equals(is));
    }

    public void testBrLoopMethNames() {
	final String is = brLoop.methNames();
	final String sb = "BranchingLoop::fooBranchingLoop::doIt";
	assertTrue("Name of available methods of " + brLoop.getFName() + " is "
		+ is + " instead of " + sb + ".", sb.equals(is));
    }

    public void testAbsMinNrOfNodes() {
	final int is = absMin.getNrOfNodes();
	final int sb = 4;
	assertTrue("\nNr of nodes of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);
    }

    public void testBrLoopNrOfNodes() {
	final int is = brLoop.getNrOfNodes();
	final int sb = 8;
	assertTrue("\nNr of nodes of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);
    }

    public void testAbsMinNrOfStatements() {
	final int is = absMin.getNrOfStatements();
	final int sb = 4;
	assertTrue("\nNr of Statements of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);
    }

    public void testBrLoopNrOfStatements() {
	final int is = brLoop.getNrOfStatements();
	final int sb = 3;
	assertTrue("\nNr of Statements of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);
    }

    public void testAbsMinNrOfMGS() {
	final int is = absMin.getNrOfMGS();
	final int sb = 4;
	assertTrue("\nNr of ModelGenerators of " + absMin.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);
    }

    public void testBrLoopNrOfMGS() {
	final int is = brLoop.getNrOfMGS();
	final int sb = 5;
	assertTrue("\nNr of ModelGenerators of " + brLoop.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);
    }

    public void testAbsMinOracleExists() {
	assertTrue("\nOracle of " + absMin.getFName() + " is null", absMin
		.isOracleNnull());
    }

    public void testBrLoopOracleExists() {
	assertTrue("\nOracle of " + brLoop.getFName() + " is null", brLoop
		.isOracleNnull());
    }

    public void testAbsMinNrOfPVS() {
	final int is = absMin.getNrOfPV();
	final int sb = 6;
	assertTrue("\nNr of ProgramVariables of " + absMin.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);
    }

    public void testBrLoopNrOfPVS() {
	final int is = brLoop.getNrOfPV();
	final int sb = 4;
	assertTrue("\nNr of ProgramVariables of " + brLoop.getFName() + " is "
		+ is + " instead of " + sb + ".", is == sb);
    }

    public void testAbsMinNrOfPVS2() {
	final int is = absMin.getNrOfPV2();
	final int sb = 6;
	assertTrue("\nNr of ProgramVariables in TestGenerator of "
		+ absMin.getFName() + " is " + is + " instead of " + sb + ".",
		is == sb);
    }

    public void testBrLoopNrOfPVS2() {
	final int is = brLoop.getNrOfPV2();
	final int sb = 8;
	assertTrue("\nNr of ProgramVariables in TestGenerator of "
		+ brLoop.getFName() + " is " + is + " instead of " + sb + ".",
		is == sb);
    }

    public void testAbsMinNrOfTesDat() {
	final int is = absMin.getNrOfTestDat();
	final int sb = 4;
	assertTrue("\nNr of Test Tuples of " + absMin.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);
    }

    public void testBrLoopNrOfTesDat() {
	final int is = brLoop.getNrOfTestDat();
	final int sb = 4;
	assertTrue("\nNr of Test Tuples of " + brLoop.getFName() + " is " + is
		+ " instead of " + sb + ".", is == sb);
    }

    public void testAbsMinData() {
	assertTrue(absMin.wrongData(), absMin.checkTestData());
    }

    public void testBrLoopData() {
	assertTrue(brLoop.wrongData(), brLoop.checkTestData());
    }

}
