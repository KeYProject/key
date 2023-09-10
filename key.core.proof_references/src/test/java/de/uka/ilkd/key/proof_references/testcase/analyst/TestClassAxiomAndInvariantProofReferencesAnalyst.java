/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.testcase.analyst;

import de.uka.ilkd.key.proof_references.analyst.ClassAxiomAndInvariantProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.proof_references.testcase.AbstractProofReferenceTestCase;

import org.junit.jupiter.api.Test;

/**
 * Tests for {@link ClassAxiomAndInvariantProofReferencesAnalyst}.
 *
 * @author Martin Hentschel
 */
public class TestClassAxiomAndInvariantProofReferencesAnalyst
        extends AbstractProofReferenceTestCase {
    /**
     * Tests "InvariantInOperationContractOfArgument".
     */
    @Test
    public void testInvariantInOperationContractOfArgument() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/InvariantInOperationContractOfArgument/InvariantInOperationContractOfArgument.java",
            "InvariantInOperationContractOfArgument", "main", false,
            new ClassAxiomAndInvariantProofReferencesAnalyst(),
            element -> IProofReference.USE_INVARIANT.equals(element.getKind()),
            new ExpectedProofReferences(IProofReference.USE_INVARIANT,
                "and(geq(int::select(heap,self,Child::$x),Z(0(#))),leq(int::select(heap,self,Child::$x),Z(0(1(#)))))<<SC>>"));
    }

    /**
     * Tests "InvariantInOperationContract".
     */
    @Test
    public void testInvariantInOperationContract() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/InvariantInOperationContract/InvariantInOperationContract.java",
            "InvariantInOperationContract", "main", false,
            new ClassAxiomAndInvariantProofReferencesAnalyst(),
            element -> IProofReference.USE_AXIOM.equals(element.getKind()),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equiv(java.lang.Object::<inv>(heap,self),not(equals(Child::select(heap,self,InvariantInOperationContract::$child),null))<<impl>>)"));
    }

    /**
     * Tests "NestedInvariantInOperationContract".
     */
    @Test
    public void testNestedInvariantInOperationContract() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/NestedInvariantInOperationContract/NestedInvariantInOperationContract.java",
            "NestedInvariantInOperationContract", "main", false,
            new ClassAxiomAndInvariantProofReferencesAnalyst(),
            element -> IProofReference.USE_AXIOM.equals(element.getKind()),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equiv(java.lang.Object::<inv>(heap,self),not(equals(ChildContainer::select(heap,self,NestedInvariantInOperationContract::$cc),null))<<impl>>)"));
    }

    /**
     * Tests "ModelFieldTest#doubleX".
     */
    @Test
    public void testModelFieldTest_doubleX() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ModelFieldTest/ModelFieldTest.java", "test.ModelFieldTest", "doubleX",
            false, new ClassAxiomAndInvariantProofReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equiv(java.lang.Object::<inv>(heap,self),true)"),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equals(test.ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,test.ModelFieldTest::$x)))"));
    }

    /**
     * Tests "ModelFieldTest#test.ModelFieldTest::$f".
     */
    @Test
    public void testModelFieldTest_f() throws Exception {
        doReferenceFunctionTest(TESTCASE_DIRECTORY,
            "/proofReferences/ModelFieldTest/ModelFieldTest.java", "test.ModelFieldTest",
            "test.ModelFieldTest::$f", false, new ClassAxiomAndInvariantProofReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equiv(java.lang.Object::<inv>(heap,self),true)"),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equals(test.ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,test.ModelFieldTest::$x)))"));
    }

    /**
     * Tests "AccessibleTest".
     */
    public void testAccessibleTest() throws Exception {
        doReferenceFunctionTest(TESTCASE_DIRECTORY,
            "/proofReferences/AccessibleTest/AccessibleTest.java", "test.B",
            "java.lang.Object::<inv>", false, new ClassAxiomAndInvariantProofReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.USE_AXIOM,
                "equiv(java.lang.Object::<inv>(heap,self),java.lang.Object::<inv>(heap,test.AccessibleTest::select(heap,self,test.B::$c)))"));
    }
}
