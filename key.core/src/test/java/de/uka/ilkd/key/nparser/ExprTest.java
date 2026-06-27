/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.peg.KeYParboiledParser;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.parsing.BuildingException;
import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;
import org.parboiled.Parboiled;
import org.parboiled.errors.InvalidInputError;
import org.parboiled.errors.ParseError;
import org.parboiled.parserunners.ReportingParseRunner;
import org.parboiled.support.MatcherPath;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.URL;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class ExprTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprTest.class);

    @ParameterizedTest
    @CsvFileSource(resources = "exprs.txt", delimiter = '^')
    public void parseAndVisit(String expr) throws IOException {
        Assumptions.assumeFalse(expr.startsWith("#"));
        KeyIO io = getIo();
        try {
            JTerm actual = io.parseExpression(expr);
            assertNotNull(actual);
            LOGGER.info("Term: {}", actual);
        } catch (BuildingException e) {
            DebugKeyLexer.debug(expr);
        }
    }

    private KeyIO getIo() throws IOException {
        Services services = new Services(new JavaProfile());
        services.activateJava(null);
        String p = "/de/uka/ilkd/key/proof/rules/ldt.key";
        URL url = getClass().getResource(p);
        Assumptions.assumeTrue(url != null);
        KeyIO io = new KeyIO(services);
        io.load(url).parseFile().loadDeclarations().loadSndDegreeDeclarations();

        NamespaceBuilder nssb = new NamespaceBuilder(services.getNamespaces());
        nssb.addVariable("aa", "int").addVariable("bb", "int").addVariable("cc", "int")
                .addProgramVariable("int", "x");

        // Without this call, the LDTs are not available to the expression
        // builder. Probably a problem of the mocking here. (MU)
        services.getTypeConverter().init();

        return io;
    }


    @ParameterizedTest
    @CsvFileSource(resources = "precedence_tests.txt", delimiterString = ":::")
    void precedenceStrongArithmetic(String actual, String expected) throws IOException {
        var io = getIo();
        var e = io.parseExpression(expected);
        var a = io.parseExpression(actual);
        assertEquals(e, a);
    }


    static KeYParboiledParser p = Parboiled.createParser(KeYParboiledParser.class);
    static ReportingParseRunner<?> x = new ReportingParseRunner<>(p.Term());

    @ParameterizedTest
    @CsvFileSource(resources = "exprs.txt", delimiter = '^')
    public void parseAndVisitPEG(String expr) {
        Assumptions.assumeFalse(expr.startsWith("#"));

        long t1 = System.nanoTime();
        ParsingFacade.createParser(ParsingFacade.createLexer(CharStreams.fromString(expr)))
                .termEOF();
        long t2 = System.nanoTime();

        long q1 = System.nanoTime();
        var r = x.run(expr);
        double q2 = System.nanoTime();


        System.out.printf("%2.2f \t\t %s\n", (q2 - q1) / (t2 - t1), r.matched);
        if (!r.matched) {
            for (ParseError it : r.parseErrors) {
                var iie = (InvalidInputError) it;
                var prefix = iie.getFailedMatchers().getFirst();
                for (MatcherPath m : iie.getFailedMatchers()) {
                    prefix = prefix.commonPrefix(m);
                }
                System.out.println(prefix);
                for (MatcherPath m : iie.getFailedMatchers()) {
                    System.out.print(m.parent.parent.element.matcher);
                    System.out.print(" :: ");
                    System.out.print(m.parent.element.matcher);
                    System.out.print(" :: ");
                    System.out.println(m.element.matcher);
                }
            }
        }

        assert r.matched;
    }

}
