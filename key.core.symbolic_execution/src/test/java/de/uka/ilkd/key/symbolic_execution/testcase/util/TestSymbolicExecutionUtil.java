/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.util;

import java.io.File;
import java.util.Map;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

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
     * Tests {@link SymbolicExecutionUtil#improveReadability(Term, Services)}
     */
    @Test
    public void test1ImproveReadability() throws ProblemLoaderException {
        File location = new File(testCaseDirectory,
            "/readability/InnerAndAnonymousTypeTest/InnerAndAnonymousTypeTest.java")
                    .getAbsoluteFile();
        assertTrue(location.exists(), "Could not find required resource: " + location);

        KeYEnvironment<?> environment = KeYEnvironment.load(location, null, null, null);
        Services services = environment.getServices();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Sort intSort = integerLDT.targetSort();
        final TermBuilder TB = services.getTermBuilder();
        // Create test terms
        Term a = TB.var(new LogicVariable(new Name("a"), intSort));
        Term b = TB.var(new LogicVariable(new Name("b"), intSort));
        Term aleqb = TB.leq(a, b);
        Term altb = TB.lt(a, b);
        Term agtb = TB.gt(a, b);
        Term ageqb = TB.geq(a, b);
        Term notAleqb = TB.not(aleqb);
        Term notAltb = TB.not(altb);
        Term notAgtb = TB.not(agtb);
        Term notAgeqb = TB.not(ageqb);
        Term onePlusB = TB.add(TB.one(), b);
        Term bPlusOne = TB.add(b, TB.one());
        Term altOnePlusB = TB.lt(a, onePlusB);
        Term altBPlusOne = TB.lt(a, bPlusOne);
        Term ageqOnePlusB = TB.geq(a, onePlusB);
        Term ageqBPlusOne = TB.geq(a, bPlusOne);
        Term minusOne = services.getTypeConverter().getIntegerLDT()
                .translateLiteral(new IntLiteral(-1), services);
        Term minusOnePlusB = TB.add(minusOne, b);
        Term bPlusMinusOne = TB.add(b, minusOne);
        Term bMinusOne = TB.func(integerLDT.getSub(), b, TB.one());
        Term aleqMinusOnePlusB = TB.leq(a, minusOnePlusB);
        Term aleqBPlusMinusOne = TB.leq(a, bPlusMinusOne);
        Term aleqBMinusOne = TB.leq(a, bMinusOne);
        Term agtMinusOnePlusB = TB.gt(a, minusOnePlusB);
        Term agtBPlusMinusOne = TB.gt(a, bPlusMinusOne);
        Term agtBMinusOne = TB.gt(a, bMinusOne);
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
        Term complex = TB.and(altOnePlusB, TB.or(ageqBPlusOne, agtMinusOnePlusB));
        Term expectedComplex = TB.and(aleqb, TB.or(agtb, ageqb));
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
            defaultSettings.put(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
            Assertions.assertEquals(defaultSettings, changedSettings);
        } finally {
            if (originalValue != null) {
                SymbolicExecutionUtil.setChoiceSetting(
                    SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalValue);
            }
        }
    }
}
