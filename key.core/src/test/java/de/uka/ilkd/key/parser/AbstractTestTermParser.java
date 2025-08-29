/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.IOException;
import java.nio.file.Path;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Class providing methods for parser tests.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class AbstractTestTermParser {

    protected final TermFactory tf;
    protected final TermBuilder tb;
    protected final NamespaceSet nss;
    protected final Services services;
    protected KeyIO io;

    public AbstractTestTermParser() {
        services = getServices();
        tb = services.getTermBuilder();
        tf = tb.tf();
        nss = services.getNamespaces();
        io = new KeyIO(services, nss);
    }

    protected Sort lookup_sort(String name) {
        return nss.sorts().lookup(new Name(name));
    }

    protected Function lookup_func(String name) {
        return nss.functions().lookup(new Name(name));
    }

    protected LogicVariable declareVar(String name, Sort sort) {
        LogicVariable v = new LogicVariable(new Name(name), sort);
        nss.variables().add(v);
        return v;
    }

    public void parseDecls(String content) throws IOException {
        io.load(content).parseFile().loadDeclarations().loadSndDegreeDeclarations();
    }

    public JTerm parseProblem(String s) {
        try {
            new Recoder2KeY(TacletForTests.services(), nss).parseSpecialClasses();
            KeyIO io = new KeyIO(TacletForTests.services(), nss);
            KeyIO.Loader loader = io.load(s);
            return loader.getProblem();
        } catch (Exception e) {
            throw new RuntimeException("Exc while Parsing", e);
        }
    }

    public JTerm parseTerm(String s) throws Exception {
        return io.parseExpression(s);
    }

    public JTerm parseFormula(String s) throws Exception {
        return parseTerm(s);
    }

    /**
     * Convert a {@link JTerm} into a {@link String}.
     *
     * @param t The {@link JTerm} that will be converted.
     */
    protected String printTerm(JTerm t) {
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.getNotationInfo().setHidePackagePrefix(false);
        lp.printTerm(t);
        return lp.result();
    }

    /**
     * Remove whitespaces before executing
     * {@link org.junit.jupiter.api.Assertions#assertEquals(Object, Object)}.
     */
    protected static void assertEqualsIgnoreWhitespaces(String expected, String actual) {
        assertEquals(expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""));
    }

    protected static void assertEqualsIgnoreWhitespaces(String message, String expected,
            String actual) {
        assertEquals(expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""), message);
    }

    protected void verifyPrettyPrinting(String expectedPrettySyntax, JTerm expectedParseResult) {
        // check whether pretty-printing the parsed term yields the original pretty syntax again
        String printedSyntax = printTerm(expectedParseResult);
        String message = ("""

                Assertion failed while pretty-printing a term:
                %s
                Expected pretty-syntax is: "%s"
                But pretty-printing resulted in: "%s"
                (whitespaces are ignored during comparison of the above strings)
                """).formatted(expectedParseResult, expectedPrettySyntax, printedSyntax);
        assertEqualsIgnoreWhitespaces(message, expectedPrettySyntax, printedSyntax);
    }

    protected void verifyParsing(JTerm expectedParseResult, String expectedPrettySyntax)
            throws Exception {
        // check whether parsing pretty-syntax produces the correct term
        JTerm parsedPrettySyntax = parseTerm(expectedPrettySyntax);
        String message = "\nAssertion failed while parsing pretty syntax. " + "Parsed string \""
            + expectedPrettySyntax + "\", which results in term:\n" + parsedPrettySyntax
            + "\nBut expected parse result is:\n" + expectedParseResult + "\n";
        assertEquals(expectedParseResult, parsedPrettySyntax, message);
    }

    /**
     * Takes two different String representations for the same term and checks whether they result
     * in the same {@link JTerm} after parsing. Subsequently, the {@link JTerm} is printed back to a
     * {@link String} and compared with the first argument. The first argument is expected to be in
     * pretty-syntax.
     *
     * @param prettySyntax {@link JTerm} representation in pretty-syntax.
     * @param verboseSyntax {@link JTerm} in verbose syntax.
     * @param optionalStringRepresentations Optionally, additional String representations will be
     *        tested for correct parsing.
     */
    protected void comparePrettySyntaxAgainstVerboseSyntax(String prettySyntax,
            String verboseSyntax, String... optionalStringRepresentations) throws Exception {
        JTerm expectedParseResult = parseTerm(verboseSyntax);
        compareStringRepresentationAgainstTermRepresentation(prettySyntax, expectedParseResult,
            optionalStringRepresentations);
    }

    /**
     * Takes a {@link String} and a {@link JTerm} and checks whether they can be transformed into
     * each other by the operations parsing and printing.
     *
     * @param prettySyntax Expected result after pretty-printing {@code expectedParseResult}.
     * @param expectedParseResult Expected result after parsing {@code expectedPrettySyntax}.
     * @param optionalStringRepresentations Optionally, additional String representations will be
     *        tested for correct parsing.
     */
    protected void compareStringRepresentationAgainstTermRepresentation(String prettySyntax,
            JTerm expectedParseResult, String... optionalStringRepresentations) throws Exception {

        verifyParsing(expectedParseResult, prettySyntax);
        verifyPrettyPrinting(prettySyntax, expectedParseResult);

        /*
         * Optionally, further string representations of the same term will be parsed here.
         */
        for (String optionalStringRepresentation : optionalStringRepresentations) {
            assertEquals(expectedParseResult, parseTerm(optionalStringRepresentation));
        }
    }

    protected Services getServices() {
        Path keyFile = HelperClassForTests.TESTCASE_DIRECTORY
                .resolve("termParser")
                .resolve("parserTest.key");
        return HelperClassForTests.createServices(keyFile);
    }

}
