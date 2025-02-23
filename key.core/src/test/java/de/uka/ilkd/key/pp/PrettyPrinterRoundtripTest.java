/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.io.File;
import java.net.URL;
import java.util.List;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Pretty printer roundtrip test.
 * <p>
 * Any term that is pretty printed and then parsed again should be equal to the original term.
 *
 * @author Mattias Ulbrich
 */
public class PrettyPrinterRoundtripTest {

    public static final Choice WITH_FINAL = new Choice("immutable", "finalFields");
    public static final Choice WITHOUT_FINAL = new Choice("onHeap", "finalFields");
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

    private static final String[] CASES = {
        "1+1",
        "-1",
        "1.1d+0d",
        "-1d",
        // "-1r",
        "-1f",
        "1.1f+0f",
        // "union(empty, empty)",
        "(1 + 2) + 3", "1 + (2 + 3)", // for associativity checks
        "(true -> true) -> true", "true -> (true -> true)", // for associativity checks
        "(true & true) & true", "true & (true & true)", // for associativity checks
    };

    private static final String[] HEAP_CASES = {
        "self.f",
        "sub.f",
        "int::select(heap, sub, C::$f)",
        "int::final(self, C::$f)",
        "\\forall Field f; int::select(heap, self, C::$f) = 0",
        "\\forall Field fvar; self.fvar = 0",
        "\\forall Field fvar; any::final(self, fvar) = 0",
        "self.finf"
    };

    public static Stream<Arguments> getCases() {
        return Stream.concat(Stream.of(CASES), Stream.of(HEAP_CASES)).map(Arguments::of);
    }

    public static Stream<Arguments> getHeapCases() {
        return Stream.of(HEAP_CASES).map(Arguments::of);
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("getCases")
    public void roundtrip(String termString) throws Exception {
        services.getProof().getSettings().getChoiceSettings().updateWith(List.of(WITH_FINAL));
        Term term = io.parseExpression(termString);
        System.out.println("Original: " + term);
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTerm(term);
        var string = lp.result();
        System.out.println("Pretty printed: " + string);
        Term term2 = io.parseExpression(string);
        System.out.println("Reparsed: " + term2);
        assertEqualModAlpha(term, term2);
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("getHeapCases")
    void roundtripWithoutFinal(String termString) throws Exception {
        services.getProof().getSettings().getChoiceSettings().updateWith(List.of(WITHOUT_FINAL));
        Term term = io.parseExpression(termString);
        System.out.println("Original: " + term);
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTerm(term);
        var string = lp.result();
        System.out.println("Pretty printed: " + string);
        Term term2 = io.parseExpression(string);
        System.out.println("Reparsed: " + term2);
        assertEqualModAlpha(term, term2);
    }

    private void assertEqualModAlpha(Term expected, Term actual) {
        var value = expected.equalsModProperty(actual, RenamingTermProperty.RENAMING_TERM_PROPERTY);
        if (!value) {
            System.err.println("Expected: " + expected);
            System.err.println("Actual  : " + actual);
        }
        assertTrue(value, "Expected: " + expected + " but was: " + actual);
    }

    private static Services getServices() {
        URL url = PrettyPrinterRoundtripTest.class.getResource("roundTripTest.key");
        assert url != null : "Could not find roundTripTest.key";
        assert "file".equals(url.getProtocol()) : "URL is not a file URL";
        File keyFile = new File(url.getPath());
        return HelperClassForTests.createServices(keyFile);
    }
}
