/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

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

    public Term parseProblem(String s) {
        try {
            new Recoder2KeY(TacletForTests.services(), nss).parseSpecialClasses();
            KeyIO io = new KeyIO(TacletForTests.services(), nss);
            KeyIO.Loader loader = io.load(s);
            return loader.getProblem();
        } catch (Exception e) {
            throw new RuntimeException("Exc while Parsing", e);
        }
    }

    public Term parseTerm(String s) throws Exception {
        return io.parseExpression(s);
    }

    public Term parseFormula(String s) throws Exception {
        return parseTerm(s);
    }

    /**
     * Convert a {@link Term} into a {@link String}.
     *
     * @param t The {@link Term} that will be converted.
     */
    protected String printTerm(Term t) {
        LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), services);
        lp.getNotationInfo().setHidePackagePrefix(false);
        lp.printTerm(t);
        return lp.result();
    }

    /**
     * Remove whitespaces before executing
     * {@link junit.framework.TestCase#assertEquals(java.lang.String, java.lang.String)}.
     */
    protected static void assertEqualsIgnoreWhitespaces(String expected, String actual) {
        assertEquals(expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""));
    }

    protected static void assertEqualsIgnoreWhitespaces(String message, String expected,
            String actual) {
        assertEquals(expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""), message);
    }

    protected void verifyPrettyPrinting(String expectedPrettySyntax, Term expectedParseResult)
            throws IOException {
        // check whether pretty-printing the parsed term yields the original pretty syntax again
        String printedSyntax = printTerm(expectedParseResult);
        String message = "\nAssertion failed while pretty-printing a term:\n" + expectedParseResult
            + "\nExpected pretty-syntax is: \"" + expectedPrettySyntax
            + "\"\nBut pretty-printing resulted in: \"" + printedSyntax
            + "\"\n(whitespaces are ignored during comparison of the above strings)\n";
        assertEqualsIgnoreWhitespaces(message, expectedPrettySyntax, printedSyntax);
    }

    protected void verifyParsing(Term expectedParseResult, String expectedPrettySyntax)
            throws Exception {
        // check whether parsing pretty-syntax produces the correct term
        Term parsedPrettySyntax = parseTerm(expectedPrettySyntax);
        String message = "\nAssertion failed while parsing pretty syntax. " + "Parsed string \""
            + expectedPrettySyntax + "\", which results in term:\n" + parsedPrettySyntax
            + "\nBut expected parse result is:\n" + expectedParseResult + "\n";
        assertEquals(expectedParseResult, parsedPrettySyntax, message);
    }

    /**
     * Takes two different String representations for the same term and checks whether they result
     * in the same {@link Term} after parsing. Subsequently, the {@link Term} is printed back to a
     * {@link String} and compared with the first argument. The first argument is expected to be in
     * pretty-syntax.
     *
     * @param prettySyntax {@link Term} representation in pretty-syntax.
     * @param verboseSyntax {@link Term} in verbose syntax.
     * @param optionalStringRepresentations Optionally, additional String representations will be
     *        tested for correct parsing.
     * @throws IOException
     */
    protected void comparePrettySyntaxAgainstVerboseSyntax(String prettySyntax,
            String verboseSyntax, String... optionalStringRepresentations) throws Exception {
        Term expectedParseResult = parseTerm(verboseSyntax);
        compareStringRepresentationAgainstTermRepresentation(prettySyntax, expectedParseResult,
            optionalStringRepresentations);
    }

    /**
     * Takes a {@link String} and a {@link Term} and checks whether they can be transformed into
     * each other by the operations parsing and printing.
     *
     * @param prettySyntax Expected result after pretty-printing {@code expectedParseResult}.
     * @param expectedParseResult Expected result after parsing {@code expectedPrettySyntax}.
     * @param optionalStringRepresentations Optionally, additional String representations will be
     *        tested for correct parsing.
     * @throws IOException
     */
    protected void compareStringRepresentationAgainstTermRepresentation(String prettySyntax,
            Term expectedParseResult, String... optionalStringRepresentations) throws Exception {

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
        File keyFile = new File(HelperClassForTests.TESTCASE_DIRECTORY + File.separator
            + "termParser" + File.separator + "parserTest.key");
        return HelperClassForTests.createServices(keyFile);
    }

}
