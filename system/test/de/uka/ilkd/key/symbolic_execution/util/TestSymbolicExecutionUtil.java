// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.io.File;
import java.util.HashMap;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;

/**
 * Tests for {@link SymbolicExecutionUtil}
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionUtil extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests {@link SymbolicExecutionUtil#improveReadability(de.uka.ilkd.key.logic.Term)}
    */
   public void testImproveReadability() {
      KeYEnvironment<?> environment = KeYEnvironment.load(new File(keyRepDirectory, "examples/_testcase/proofReferences/InnerAndAnonymousTypeTest"), null, null);
      try {
         Services services = environment.getServices();
         IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
         Sort intSort = integerLDT.targetSort();
         final TermBuilder TB = TermBuilder.DF;
         // Create test terms
         Term a = TB.var(new LogicVariable(new Name("a"), intSort));
         Term b = TB.var(new LogicVariable(new Name("b"), intSort));
         Term aleqb = TB.leq(a, b, services);
         Term altb = TB.lt(a, b, services);
         Term agtb = TB.gt(a, b, services);
         Term ageqb = TB.geq(a, b, services);
         Term notAleqb = TB.not(aleqb);
         Term notAltb = TB.not(altb);
         Term notAgtb = TB.not(agtb);
         Term notAgeqb = TB.not(ageqb);
         Term onePlusB = TB.add(services, TB.one(services), b);
         Term bPlusOne = TB.add(services, b, TB.one(services));
         Term altOnePlusB = TB.lt(a, onePlusB, services);
         Term altBPlusOne = TB.lt(a, bPlusOne, services);
         Term ageqOnePlusB = TB.geq(a, onePlusB, services);
         Term ageqBPlusOne = TB.geq(a, bPlusOne, services);
         Term minusOne = services.getTypeConverter().getIntegerLDT().translateLiteral(new IntLiteral(-1), services);
         Term minusOnePlusB = TB.add(services, minusOne, b);
         Term bPlusMinusOne = TB.add(services, b, minusOne);
         Term bMinusOne = TB.func(integerLDT.getSub(), b, TB.one(services));
         Term aleqMinusOnePlusB = TB.leq(a, minusOnePlusB, services);
         Term aleqBPlusMinusOne = TB.leq(a, bPlusMinusOne, services);
         Term aleqBMinusOne = TB.leq(a, bMinusOne, services);
         Term agtMinusOnePlusB = TB.gt(a, minusOnePlusB, services);
         Term agtBPlusMinusOne = TB.gt(a, bPlusMinusOne, services);
         Term agtBMinusOne = TB.gt(a, bMinusOne, services);
         // Test null
         assertNull(SymbolicExecutionUtil.improveReadability(null, services));
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
         assertTerm(agtb, SymbolicExecutionUtil.improveReadability(TermBuilder.DF.not(altOnePlusB), services));
         assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(TermBuilder.DF.not(ageqOnePlusB), services));
         assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(TermBuilder.DF.not(aleqBPlusMinusOne), services));
         assertTerm(altb, SymbolicExecutionUtil.improveReadability(TermBuilder.DF.not(agtBMinusOne), services));
         // Test complex term
         Term complex = TermBuilder.DF.and(altOnePlusB,
                                           TermBuilder.DF.or(ageqBPlusOne, agtMinusOnePlusB));
         Term expectedComplex = TermBuilder.DF.and(aleqb,
                                                   TermBuilder.DF.or(agtb, ageqb));
         assertTerm(expectedComplex, SymbolicExecutionUtil.improveReadability(complex, services));
      }
      finally {
         environment.dispose();
      }
   }

   /**
    * Tests {@link SymbolicExecutionUtil#getChoiceSetting(String)} and
    * {@link SymbolicExecutionUtil#setChoiceSetting(String, String)} and
    * {@link SymbolicExecutionUtil#isChoiceSettingInitialised()}.
    */
   public void testGetAndSetChoiceSetting() throws Exception {
      String originalValue = null; 
      try {
         assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
         // Store default choice settings
         HashMap<String, String> defaultSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         assertFalse(defaultSettings.isEmpty());
         // Test initial value
         originalValue = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertTrue(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW.equals(originalValue) || SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN.equals(originalValue));
         // Change value and make sure that it has changed
         String newValue = SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW.equals(originalValue) ? SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN : SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW; 
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
         assertEquals(newValue, SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS));
         // Make sure that all other settings are unchanged.
         HashMap<String, String> changedSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         defaultSettings.put(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
         assertEquals(defaultSettings, changedSettings);
      }
      finally {
         if (originalValue != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalValue);
         }
      }
   }
}