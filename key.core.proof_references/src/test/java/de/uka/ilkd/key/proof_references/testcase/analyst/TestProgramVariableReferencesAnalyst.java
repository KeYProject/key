/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.testcase.analyst;

import de.uka.ilkd.key.proof_references.analyst.ProgramVariableReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.proof_references.testcase.AbstractProofReferenceTestCase;

import org.junit.jupiter.api.Test;

/**
 * Tests for {@link ProgramVariableReferencesAnalyst}.
 *
 * @author Martin Hentschel
 */
public class TestProgramVariableReferencesAnalyst extends AbstractProofReferenceTestCase {
    /**
     * Tests "ConditionalsAndOther#forEquals".
     */
    @Test
    public void testConditionalsAndOther_forEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "forEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#forBoolean".
     */
    @Test
    public void testConditionalsAndOther_forBoolean() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "forBoolean", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#doWhileEquals".
     */
    @Test
    public void testConditionalsAndOther_doWhileEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "doWhileEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#doWhileBoolean".
     */
    @Test
    public void testConditionalsAndOther_doWhileBoolean() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "doWhileBoolean", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#whileEquals".
     */
    @Test
    public void testConditionalsAndOther_whileEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "whileEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#whileBoolean".
     */
    @Test
    public void testConditionalsAndOther_whileBoolean() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "whileBoolean", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#throwsNestedException".
     */
    @Test
    public void testConditionalsAndOther_throwsNestedException() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "throwsNestedException", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::ew"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "ConditionalsAndOther.ExceptionWrapper::wrapped"));
    }

    /**
     * Tests "ConditionalsAndOther#throwsException".
     */
    @Test
    public void testConditionalsAndOther_throwsException() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "throwsException", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::e"));
    }

    /**
     * Tests "ConditionalsAndOther#methodCallCondtional".
     */
    @Test
    public void testConditionalsAndOther_methodCallConditional() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "methodCallCondtional", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#methodCallAssignment".
     */
    @Test
    public void testConditionalsAndOther_methodCallAssignment() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "methodCallAssignment", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#methodCall".
     */
    @Test
    public void testConditionalsAndOther_methodCall() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "methodCall", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#returnComplex".
     */
    @Test
    public void testConditionalsAndOther_returnComplex() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "returnComplex", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#returnEquals".
     */
    @Test
    public void testConditionalsAndOther_returnEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "returnEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#returnBoolean".
     */
    @Test
    public void testConditionalsAndOther_returnBoolean() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "returnBoolean", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#questionIncrementsAndDecrements".
     */
    @Test
    public void testConditionalsAndOther_questionIncrementsAndDecrements() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionIncrementsAndDecrements", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"));
    }

    /**
     * Tests "ConditionalsAndOther#ifIncrementsAndDecrements".
     */
    @Test
    public void testConditionalsAndOther_ifIncrementsAndDecrements() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifIncrementsAndDecrements", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"));
    }

    /**
     * Tests "ConditionalsAndOther#questionGreater".
     */
    @Test
    public void testConditionalsAndOther_questionGreater() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionGreater", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#questionGreaterEquals".
     */
    @Test
    public void testConditionalsAndOther_questionGreaterEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionGreaterEquals", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#questionNotEquals".
     */
    @Test
    public void testConditionalsAndOther_questionNotEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionNotEquals", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#questionEquals".
     */
    @Test
    public void testConditionalsAndOther_questionEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#questionLessEquals".
     */
    @Test
    public void testConditionalsAndOther_questionLessEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionLessEquals", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#questionLess".
     */
    @Test
    public void testConditionalsAndOther_questionLess() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionLess", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#questionBoolean".
     */
    @Test
    public void testConditionalsAndOther_questionBoolean() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "questionBoolean", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#ifGreater".
     */
    @Test
    public void testConditionalsAndOther_ifGreater() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifGreater", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#ifGreaterEquals".
     */
    @Test
    public void testConditionalsAndOther_ifGreaterEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifGreaterEquals", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#ifNotEquals".
     */
    @Test
    public void testConditionalsAndOther_ifNotEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifNotEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#ifEquals".
     */
    @Test
    public void testConditionalsAndOther_ifEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#ifLessEquals".
     */
    @Test
    public void testConditionalsAndOther_ifLessEquals() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifLessEquals", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#ifLess".
     */
    @Test
    public void testConditionalsAndOther_ifLess() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifLess", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::y"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ConditionalsAndOther#ifBoolean".
     */
    @Test
    public void testConditionalsAndOther_ifBoolean() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "ifBoolean", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::b"));
    }

    /**
     * Tests "ConditionalsAndOther#switchInt".
     */
    @Test
    public void testConditionalsAndOther_switchInt() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/ConditionalsAndOther/ConditionalsAndOther.java",
            "ConditionalsAndOther", "switchInt", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ConditionalsAndOther::x"));
    }

    /**
     * Tests "ArrayLength".
     */
    @Test
    public void testArrayLength() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/ArrayLength/ArrayLength.java",
            "ArrayLength", "main", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "ArrayLength::length"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ArrayLength::array"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ArrayLength::my"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ArrayLength.MyClass::length"),
            new ExpectedProofReferences(IProofReference.ACCESS, "ArrayLength.MyClass::array"));
    }

    /**
     * Tests "Assignments#assignmentWithSelf".
     */
    @Test
    public void testAssignments_assignmentWithSelf() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "assignmentWithSelf", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::next"));
    }

    /**
     * Tests "Assignments#nestedArray".
     */
    @Test
    public void testAssignments_nestedArray() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "nestedArray", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::myClass"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments.MyClass::child"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "Assignments.MyChildClass::childArray"));
    }

    /**
     * Tests "Assignments#nestedValueAdd".
     */
    @Test
    public void testAssignments_nestedValueAdd() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "nestedValueAdd", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::myClass"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments.MyClass::child"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "Assignments.MyChildClass::thirdChildValue"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "Assignments.MyChildClass::anotherChildValue"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "Assignments.MyChildClass::childValue"));
    }

    /**
     * Tests "Assignments#nestedValue".
     */
    @Test
    public void testAssignments_nestedValue() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "nestedValue", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::myClass"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments.MyClass::child"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "Assignments.MyChildClass::anotherChildValue"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "Assignments.MyChildClass::childValue"));
    }

    /**
     * Tests "Assignments#assign".
     */
    @Test
    public void testAssignments_assign() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "assign", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#mod".
     */
    @Test
    public void testAssignments_mod() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "mod", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#div".
     */
    @Test
    public void testAssignments_div() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "div", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#mul".
     */
    @Test
    public void testAssignments_mul() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "mul", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#sub".
     */
    @Test
    public void testAssignments_sub() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "sub", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#add".
     */
    @Test
    public void testAssignments_add() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "add", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#decrementArrayBegin".
     */
    @Test
    public void testAssignments_decrementArrayBegin() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "decrementArrayBegin", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::array"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"));
    }

    /**
     * Tests "Assignments#decrementArrayEnd".
     */
    @Test
    public void testAssignments_decrementArrayEnd() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "decrementArrayEnd", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::array"),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::anotherValue"));
    }

    /**
     * Tests "Assignments#incrementArrayBegin".
     */
    @Test
    public void testAssignments_incrementArrayBegin() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "incrementArrayBegin", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::array"));
    }

    /**
     * Tests "Assignments#incrementArrayEnd".
     */
    @Test
    public void testAssignments_incrementArrayEnd() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "incrementArrayEnd", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::array"));
    }

    /**
     * Tests "Assignments#decrementBegin".
     */
    @Test
    public void testAssignments_decrementBegin() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "decrementBegin", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#decrementEnd".
     */
    @Test
    public void testAssignments_decrementEnd() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "decrementEnd", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#incrementBegin".
     */
    @Test
    public void testAssignments_incrementBegin() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "incrementBegin", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "Assignments#incrementEnd".
     */
    @Test
    public void testAssignments_incrementEnd() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/Assignments/Assignments.java",
            "Assignments", "incrementEnd", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "Assignments::value"));
    }

    /**
     * Tests "assignment".
     */
    @Test
    public void testAssignment() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY, "/proofReferences/assignment/Assignment.java",
            "assignment.Assignment", "caller", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "assignment.Assignment::b"),
            new ExpectedProofReferences(IProofReference.ACCESS, "assignment.Enum::b"));
    }

    /**
     * Tests "assignment_array2".
     */
    @Test
    public void testAssignment_array2() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_array2/Assignment_array2.java",
            "assignment_array2.Assignment_array2", "caller", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_array2.Assignment_array2::index"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_array2.Assignment_array2::as"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_array2.Assignment_array2::val"));
    }

    /**
     * Tests "assignment_read_attribute".
     */
    @Test
    public void testAssignment_read_attribute() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_read_attribute/Assignment_read_attribute.java",
            "assignment_read_attribute.Assignment_read_attribute", "caller", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_read_attribute.Class::b"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_read_attribute.Class::a"));
    }

    /**
     * Tests "assignment_read_length".
     */
    @Test
    public void testAssignment_read_length() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_read_length/Assignment_read_length.java",
            "assignment_read_length.Assignment_read_length", "caller", false,
            new ProgramVariableReferencesAnalyst(), new ExpectedProofReferences(
                IProofReference.ACCESS, "assignment_read_length.Assignment_read_length::b"));
    }

    /**
     * Tests "assignment_to_primitive_array_component".
     */
    @Test
    public void testAssignment_to_primitive_array_component() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_to_primitive_array_component/Assignment_to_primitive_array_component.java",
            "assignment_to_primitive_array_component.Assignment_to_primitive_array_component",
            "caller", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_to_primitive_array_component.Assignment_to_primitive_array_component::index"),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_to_primitive_array_component.Assignment_to_primitive_array_component::bs"));
    }

    /**
     * Tests "assignment_to_reference_array_component".
     */
    @Test
    public void testAssignment_to_reference_array_component() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_to_reference_array_component/Assignment_to_reference_array_component.java",
            "assignment_to_reference_array_component.Assignment_to_reference_array_component",
            "caller", false, new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_to_reference_array_component.Assignment_to_reference_array_component::bs"));
    }

    /**
     * Tests "assignment_write_attribute".
     */
    @Test
    public void testAssignment_write_attribute() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_write_attribute/Assignment_write_attribute.java",
            "assignment_write_attribute.Assignment_write_attribute", "caller", false,
            new ProgramVariableReferencesAnalyst(), new ExpectedProofReferences(
                IProofReference.ACCESS, "assignment_write_attribute.Class::a"));
    }

    /**
     * Tests "assignment_write_static_attribute".
     */
    @Test
    public void testAssignment_write_static_attribute() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/assignment_write_static_attribute/Assignment_write_static_attribute.java",
            "assignment_write_static_attribute.Assignment_write_static_attribute", "caller", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS,
                "assignment_write_static_attribute.Assignment_write_static_attribute::b"));
    }

    /**
     * Tests "activeUseStaticFieldReadAccess2".
     */
    @Test
    public void testActiveUseStaticFieldReadAccess2() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/activeUseStaticFieldReadAccess2/ActiveUseStaticFieldReadAccess2.java",
            "activeUseStaticFieldReadAccess2.ActiveUseStaticFieldReadAccess2", "caller", false,
            new ProgramVariableReferencesAnalyst(), new ExpectedProofReferences(
                IProofReference.ACCESS, "activeUseStaticFieldReadAccess2.Class::i"));
    }

    /**
     * Tests "activeUseStaticFieldWriteAccess2".
     */
    @Test
    public void testActiveUseStaticFieldWriteAccess2() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/activeUseStaticFieldWriteAccess2/ActiveUseStaticFieldWriteAccess2.java",
            "activeUseStaticFieldWriteAccess2.ActiveUseStaticFieldWriteAccess2", "caller", false,
            new ProgramVariableReferencesAnalyst(), new ExpectedProofReferences(
                IProofReference.ACCESS, "activeUseStaticFieldWriteAccess2.Class::a"));
    }

    /**
     * Tests "eval_order_access4".
     */
    @Test
    public void testEval_order_access4() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/eval_order_access4/Eval_order_access4.java",
            "eval_order_access4.Eval_order_access4", "caller", false,
            new ProgramVariableReferencesAnalyst(),
            new ExpectedProofReferences(IProofReference.ACCESS, "eval_order_access4.Class::a"));
    }

    /**
     * Tests "eval_order_array_access5".
     */
    @Test
    public void testEval_order_array_access5() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/eval_order_array_access5/Eval_order_array_access5.java",
            "eval_order_array_access5.Eval_order_array_access5", "caller", false,
            new ProgramVariableReferencesAnalyst(), new ExpectedProofReferences(
                IProofReference.ACCESS, "eval_order_array_access5.Class::a"));
    }

    /**
     * Tests "variableDeclarationAssign".
     */
    @Test
    public void testVariableDeclarationAssign() throws Exception {
        doReferenceMethodTest(TESTCASE_DIRECTORY,
            "/proofReferences/variableDeclarationAssign/VariableDeclarationAssign.java",
            "variableDeclarationAssign.VariableDeclarationAssign", "caller", false,
            new ProgramVariableReferencesAnalyst(), new ExpectedProofReferences(
                IProofReference.ACCESS, "variableDeclarationAssign.VariableDeclarationAssign::a"));
    }
}
