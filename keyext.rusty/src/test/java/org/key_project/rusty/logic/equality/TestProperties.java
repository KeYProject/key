/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.equality;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.NameAbstractionTable;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.proof.init.RustProfile;
import org.key_project.rusty.util.TacletForTests;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.key_project.rusty.logic.equality.RenamingProgramElementProperty.RENAMING_PROGRAM_ELEMENT_PROPERTY;

@DisplayName("Tests for different equality properties")
public class TestProperties {

    private record ProgramTuple(RustyProgramElement program1, RustyProgramElement program2) {
    }

    private ProgramTuple getPrograms(String termString1, String termString2) {
        var t1 = TacletForTests.parseTerm(termString1);
        var t2 = TacletForTests.parseTerm(termString2);

        var p1 = ((Modality) t1.op()).program().program();
        var p2 = ((Modality) t2.op()).program().program();

        return new ProgramTuple(p1, p2);
    }

    @BeforeAll
    static void setUp() {
        TacletForTests.clear();
        TacletForTests.parse(new RustProfile());
    }

    @DisplayName("Tests for RenamingProgramElementProperty")
    @Nested
    class TestRenamingProgramElementProperty {

        @DisplayName("Tests for ArithLogicalExpression")
        @Nested
        class TestArithLogicalExpression {
            @Test
            void testDifferentOperatorSameExpressions() {
                ProgramTuple programs =
                    getPrograms("\\<{ 1u32 + 2u32 }\\>true", "\\<{ 1u32 - 2u32 }\\>true");
                assertFalse(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Different operators should not be equal");
            }

            @Test
            void testSameOperatorSameExpressions() {
                ProgramTuple programs =
                    getPrograms("\\<{ -1i32 + 2i32 }\\>true", "\\<{ -1i32 + 2i32 }\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Same operators and expressions should be equal");
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");

            }
        }

        @DisplayName("Tests for NegationExpression")
        @Nested
        class TestNegationExpression {
            // @Test
            // void testDifferentOperatorSameExpression() {
            // ProgramTuple programs = getPrograms("\\<{ !true }\\>true", "\\<{ -true }\\>true");
            // assertFalse(
            // RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
            // programs.program2,
            // new NameAbstractionTable()),
            // "Different operators should not be equal");
            // }

            @Test
            void testSameOperatorSameExpression() {
                ProgramTuple programs = getPrograms("\\<{ !false }\\>true", "\\<{ !false }\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Same operators and expressions should be equal");
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");
            }

            @Test
            void testSameOperatorDifferentExpression() {
                ProgramTuple programs = getPrograms("\\<{ !false }\\>true", "\\<{ !true }\\>true");
                assertFalse(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Same operator but different expressions should not be equal");
            }
        }

        @DisplayName("Tests for ComparisonExpression")
        @Nested
        class TestComparisonExpression {
            @Test
            void testDifferentOperatorSameExpressions() {
                ProgramTuple programs =
                    getPrograms("\\<{ 1u32 < 2u32 }\\>true", "\\<{ 1u32 > 2u32 }\\>true");
                assertFalse(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Different operators should not be equal");
            }

            @Test
            void testSameOperatorSameExpressions() {
                ProgramTuple programs =
                    getPrograms("\\<{ 1u32 <= 2u32 }\\>true", "\\<{ 1u32 <= 2u32 }\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Same operators and expressions should be equal");
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");
            }
        }

        @DisplayName("Tests for CompoundAssignmentExpression")
        @Nested
        class TestCompoundAssignmentExpression {
            @Test
            void testDifferentOperatorSameExpressions() {
                ProgramTuple programs =
                    getPrograms("\\<{ i += 5u32 }\\>true", "\\<{ i -= 5u32 }\\>true");
                assertFalse(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Different operators should not be equal");
            }

            @Test
            void testSameOperatorSameExpressions() {
                ProgramTuple programs =
                    getPrograms("\\<{ i *= 5u32 }\\>true", "\\<{ i *= 5u32 }\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()));
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");
            }
        }

        @DisplayName("Test different mechanics with simple programs")
        @Nested
        class TestSimplePrograms {
            @Test
            public void testLetDifferentNames() {
                ProgramTuple programs = getPrograms("\\<{ let i: u32 = 5u32; 1u32 }\\>true",
                    "\\<{ let j: u32 = 5u32; 1u32 }\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Singular let statement with different names should be equal modulo renaming");
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");
            }

            @Test
            void testMultipleLetAndAssignment() {
                ProgramTuple programs = getPrograms(
                    "\\<{ let mut i: u32 = 0u32; let mut j: u32 = 1u32; i = 2u32; j = i; 1u32}\\>true",
                    "\\<{ let mut i: u32 = 0u32; let mut k: u32 = 1u32; i = 2u32; k = i; 1u32}\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Programs should be equal as only the variable name differs");
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");
            }

            @Test
            void testAssignmentShadowedVariable() {
                ProgramTuple programs = getPrograms(
                    "\\<{ let mut i: u32 = 0u32; let mut i: u32 = 1u32; i = 2u32; 1u32}\\>true",
                    "\\<{ let mut j: u32 = 0u32; let mut k: u32 = 1u32; k = 2u32; 1u32}\\>true");
                assertTrue(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(programs.program1,
                        programs.program2,
                        new NameAbstractionTable()),
                    "Programs should be equal as i is shadowed by the second declaration and j is never used");
                assertEquals(
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program1),
                    RENAMING_PROGRAM_ELEMENT_PROPERTY.hashCodeModThisProperty(programs.program2),
                    "Hashcodes should be equal for equal programs");
            }
        }
    }
}
