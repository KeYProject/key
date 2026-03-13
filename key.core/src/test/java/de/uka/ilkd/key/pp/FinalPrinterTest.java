/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.nparser.KeyIO;

import org.key_project.logic.Choice;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Mattias Ulbrich
 */

public class FinalPrinterTest {

    public static final Choice WITHOUT_FINAL = new Choice("finalFields", "onHeap");
    private static KeyIO io;
    private static Services services;

    @BeforeAll
    public static void setup() {
        services = getServices();
        io = new KeyIO(services, services.getNamespaces());
    }

    @AfterAll
    public static void tearDown() {
        io = null;
    }

    @ParameterizedTest(name = "{0} => {1}")
    @CsvSource(delimiter = ';', textBlock = """
            int::select(heap, self, C::$f); self.f
            int::select(heap, self, C::$finf); int::select(heap, self, C::$finf)
            int::final(sub, Csub::$finf); sub.finf
            int::final(sub, C::$finf); sub.(C::finf)
            int::final(self, C::$finf); self.finf
            int::final(sub, C::$finf); sub.(C::finf)
            """)
    public void testPPWithFinal(String termString, String expected) throws Exception {
        services.getProof().getSettings().getChoiceSettings()
                .updateWith(List.of(PrettyPrinterRoundtripTest.WITH_FINAL));
        JTerm term = io.parseExpression(termString);
        System.out.println("Original: " + term);
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTerm(term);
        var printed = lp.result();
        assertEquals(expected, printed);
    }

    @ParameterizedTest(name = "{0} => {1}")
    @CsvSource(delimiter = ';', textBlock = """
            int::final(sub, Csub::$finf); sub.finf
            int::final(sub, C::$finf); sub.(C::finf)
            int::final(self, C::$finf); self.finf
            int::select(heap, self, C::$f); self.f
            int::select(heap, self, C::$finf); self.finf
            """)
    public void testPPWithoutFinal(String termString, String expected) throws Exception {
        services.getProof().getSettings().getChoiceSettings()
                .updateWith(List.of(PrettyPrinterRoundtripTest.WITHOUT_FINAL));
        JTerm term = io.parseExpression(termString);
        System.out.println("Original: " + term);
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTerm(term);
        var printed = lp.result();
        assertEquals(expected, printed);
    }


    private void assertEqualModAlpha(JTerm expected, JTerm actual) {
        var value =
            RenamingTermProperty.RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, actual);
        if (!value) {
            System.err.println("Expected: " + expected);
            System.err.println("Actual  : " + actual);
        }
        assertTrue(value, "Expected: " + expected + " but was: " + actual);
    }

    private static Services getServices() {
        return PrettyPrinterRoundtripTest.getServices();
    }
}
