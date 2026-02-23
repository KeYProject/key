/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.util;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.MethodOrderer;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestMethodOrder;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link SymbolicExecutionUtil}
 *
 * @author Martin Hentschel
 */
@TestMethodOrder(MethodOrderer.MethodName.class)
public class TestSymbolicExecutionUtil extends AbstractSymbolicExecutionTestCase {
    /**
     * Tests {@link SymbolicExecutionUtil#improveReadability(JTerm, Services)}
     */
    @Test
    public void test1ImproveReadability() throws ProblemLoaderException {
        Path location = testCaseDirectory.resolve(
            "readability/InnerAndAnonymousTypeTest/InnerAndAnonymousTypeTest.java")
                .toAbsolutePath();
        assertTrue(Files.exists(location), "Could not find required resource: " + location);

        KeYEnvironment<?> environment = KeYEnvironment.load(location, null, null, null);
        Services services = environment.getServices();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Sort intSort = integerLDT.targetSort();
        final TermBuilder TB = services.getTermBuilder();
        // Create test terms
        JTerm a = TB.var(new LogicVariable(new Name("a"), intSort));
        JTerm b = TB.var(new LogicVariable(new Name("b"), intSort));
        JTerm aleqb = TB.leq(a, b);
        JTerm altb = TB.lt(a, b);
        JTerm agtb = TB.gt(a, b);
        JTerm ageqb = TB.geq(a, b);
        JTerm notAleqb = TB.not(aleqb);
        JTerm notAltb = TB.not(altb);
        JTerm notAgtb = TB.not(agtb);
        JTerm notAgeqb = TB.not(ageqb);
        JTerm onePlusB = TB.add(TB.one(), b);
        JTerm bPlusOne = TB.add(b, TB.one());
        JTerm altOnePlusB = TB.lt(a, onePlusB);
        JTerm altBPlusOne = TB.lt(a, bPlusOne);
        JTerm ageqOnePlusB = TB.geq(a, onePlusB);
        JTerm ageqBPlusOne = TB.geq(a, bPlusOne);
        JTerm minusOne = services.getTypeConverter().getIntegerLDT()
                .translateLiteral(new IntLiteral(-1), services);
        JTerm minusOnePlusB = TB.add(minusOne, b);
        JTerm bPlusMinusOne = TB.add(b, minusOne);
        JTerm bMinusOne = TB.func(integerLDT.getSub(), b, TB.one());
        JTerm aleqMinusOnePlusB = TB.leq(a, minusOnePlusB);
        JTerm aleqBPlusMinusOne = TB.leq(a, bPlusMinusOne);
        JTerm aleqBMinusOne = TB.leq(a, bMinusOne);
        JTerm agtMinusOnePlusB = TB.gt(a, minusOnePlusB);
        JTerm agtBPlusMinusOne = TB.gt(a, bPlusMinusOne);
        JTerm agtBMinusOne = TB.gt(a, bMinusOne);
        // Test null
        Assertions.assertNull(SymbolicExecutionUtil.improveReadability(null, services));
        assertTerm(notAleqb, SymbolicExecutionUtil.improveReadability(notAleqb, null));
        // Test simple ! <, ! <=, ! >, ! >= improvements
        assertTerm(agtb, SymbolicExecutionUtil.improveReadability(notAleqb, services));
        assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(notAltb, services));
        assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(notAgtb, services));
        assertTerm(altb, SymbolicExecutionUtil.improveReadability(notAgeqb, services));
        // Test < 1 +, < + 1
        assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(altOnePlusB, services));
        assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(altBPlusOne, services));
        // Test >= 1 +, >= + 1
        assertTerm(agtb, SymbolicExecutionUtil.improveReadability(ageqOnePlusB, services));
        assertTerm(agtb, SymbolicExecutionUtil.improveReadability(ageqBPlusOne, services));
        // Test <= -1 +, <= + -1
        assertTerm(altb, SymbolicExecutionUtil.improveReadability(aleqMinusOnePlusB, services));
        assertTerm(altb, SymbolicExecutionUtil.improveReadability(aleqBPlusMinusOne, services));
        assertTerm(altb, SymbolicExecutionUtil.improveReadability(aleqBMinusOne, services));
        // Test > -1 +, > + -1
        assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(agtMinusOnePlusB, services));
        assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(agtBPlusMinusOne, services));
        assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(agtBMinusOne, services));
        // Test combined
        assertTerm(agtb, SymbolicExecutionUtil.improveReadability(TB.not(altOnePlusB), services));
        assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(TB.not(ageqOnePlusB), services));
        assertTerm(ageqb,
            SymbolicExecutionUtil.improveReadability(TB.not(aleqBPlusMinusOne), services));
        assertTerm(altb, SymbolicExecutionUtil.improveReadability(TB.not(agtBMinusOne), services));
        // Test complex term
        JTerm complex = TB.and(altOnePlusB, TB.or(ageqBPlusOne, agtMinusOnePlusB));
        JTerm expectedComplex = TB.and(aleqb, TB.or(agtb, ageqb));
        assertTerm(expectedComplex, SymbolicExecutionUtil.improveReadability(complex, services));
        environment.dispose();
    }

    /**
     * Tests {@link SymbolicExecutionUtil#getChoiceSetting(String)} and
     * {@link SymbolicExecutionUtil#setChoiceSetting(String, String)} and
     * {@link SymbolicExecutionUtil#isChoiceSettingInitialised()}.
     */
    @Test
    public void test2GetAndSetChoiceSetting() {
        String originalValue = null;
        try {
            // weigl: disable, no clue why the choice settings should be initialised
            // assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
            // Store default choice settings
            Map<String, String> defaultSettings =
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
            // weigl: disable, no clue why the choice settings should be initialised
            // assertFalse(defaultSettings.isEmpty());
            // Test initial value
            originalValue = SymbolicExecutionUtil
                    .getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
            assertTrue(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW
                    .equals(originalValue)
                    || SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN
                            .equals(originalValue));
            // Change value and make sure that it has changed
            String newValue = SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW
                    .equals(originalValue)
                            ? SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN
                            : SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW;
            SymbolicExecutionUtil.setChoiceSetting(
                SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
            Assertions.assertEquals(newValue, SymbolicExecutionUtil
                    .getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS));
            // Make sure that all other settings are unchanged.
            Map<String, String> changedSettings =
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();

            Map<String, String> expectedSettings = new HashMap<>();
            expectedSettings.putAll(defaultSettings);
            expectedSettings.put(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);

            Assertions.assertEquals(expectedSettings, changedSettings);
        } finally {
            if (originalValue != null) {
                SymbolicExecutionUtil.setChoiceSetting(
                    SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalValue);
            }
        }
    }
}
