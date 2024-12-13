package de.uka.ilkd.key.pp;

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

import java.io.File;
import java.net.URL;
import java.util.List;
import java.util.stream.Stream;

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

    public static Stream<Arguments> casesWithFinal() {
        return Stream.of(
                Arguments.of("int::select(heap, self, C::$f)", "self.f"),
                Arguments.of("int::select(heap, self, C::$finf)", "int::select(heap, self, C::$finf)"),
                Arguments.of("int::final(sub, Csub::$finf)", "sub.finf"),
                Arguments.of("int::final(sub, C::$finf)", "sub.(C::finf)"),
                Arguments.of("int::final(self, C::$finf)", "self.finf"),
                Arguments.of("int::final(sub, C::$finf)", "sub.(C::finf)")
        );
    }

    @ParameterizedTest(name = "{0} => {1}")
    @MethodSource("casesWithFinal")
    public void testPPWithFinal(String termString, String expected) throws Exception {
        services.getProof().getSettings().getChoiceSettings().updateWith(List.of(PPRoundtripTest.WITH_FINAL));
        Term term = io.parseExpression(termString);
        System.out.println("Original: " + term);
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTerm(term);
        var printed = lp.result();
        assertEquals(expected, printed);
    }

    public static Stream<Arguments> casesWithoutFinal() {
        return Stream.of(
                Arguments.of("int::final(sub, Csub::$finf)", "sub.finf"),
                Arguments.of("int::final(sub, C::$finf)", "sub.(C::finf)"),
                Arguments.of("int::final(self, C::$finf)", "self.finf"),
                Arguments.of("int::select(heap, self, C::$f)", "self.f"),
                Arguments.of("int::select(heap, self, C::$finf)", "self.finf")
                );
    }


    @ParameterizedTest(name = "{0} => {1}")
    @MethodSource("casesWithoutFinal")
    public void testPPWithoutFinal(String termString, String expected) throws Exception {
        services.getProof().getSettings().getChoiceSettings().updateWith(List.of(PPRoundtripTest.WITHOUT_FINAL));
        Term term = io.parseExpression(termString);
        System.out.println("Original: " + term);
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.printTerm(term);
        var printed = lp.result();
        assertEquals(expected, printed);
    }


    private void assertEqualModAlpha(Term expected, Term actual) {
        var value = expected.equalsModProperty(actual, RenamingTermProperty.RENAMING_TERM_PROPERTY);
        if(!value) {
            System.err.println("Expected: " + expected);
            System.err.println("Actual  : " + actual);
        }
        assertTrue(value, "Expected: " + expected + " but was: " + actual);
    }

    private static Services getServices() {
        URL url = de.uka.ilkd.key.pp.PPRoundtripTest.class.getResource("roundTripTest.key");
        assert url != null : "Could not find roundTripTest.key";
        assert "file".equals(url.getProtocol()) : "URL is not a file URL";
        File keyFile = new File(url.getPath());
        return HelperClassForTests.createServices(keyFile);
    }
}
