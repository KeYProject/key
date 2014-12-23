package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import junit.framework.TestCase;

/**
 * Common code of classes {@link TestTermParser} and {@link TestTermParserHeap}
 * and {@link TestTermParserSequence}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class AbstractTestTermParser extends TestCase {

    protected final TermFactory tf;
    protected final TermBuilder tb;
    protected final NamespaceSet nss;
    protected final Services services;

    AbstractTestTermParser(String name) {
        super(name);
        services = getServices();
        tb = services.getTermBuilder();
        tf = tb.tf();
        nss = services.getNamespaces();
    }

    Sort lookup_sort(String name) {
        return (Sort) nss.sorts().lookup(new Name(name));
    }

    Function lookup_func(String name) {
        return (Function) nss.functions().lookup(new Name(name));
    }

    LogicVariable declareVar(String name, Sort sort) {
        LogicVariable v = new LogicVariable(new Name(name), sort);
        nss.variables().add(v);
        return v;
    }

    private KeYParserF stringDeclParser(String s) {
        // fills namespaces 
        new Recoder2KeY(services, nss).parseSpecialClasses();
        return new KeYParserF(ParserMode.DECLARATION,
                new KeYLexerF(s,
                        "No file. Call of parser from parser/TestTermParser.java"),
                services, nss);
    }

    public void parseDecls(String s) {
        try {
            KeYParserF stringDeclParser = stringDeclParser(s);
            stringDeclParser.decls();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw (RuntimeException) new RuntimeException("Exc while Parsing:\n" + sw).initCause(e);
        }
    }

    public Term parseProblem(String s) {
        try {
            new Recoder2KeY(TacletForTests.services(),
                    nss).parseSpecialClasses();
            return new KeYParserF(ParserMode.PROBLEM,
                    new KeYLexerF(s,
                            "No file. Call of parser from parser/TestTermParser.java"),
                    new ParserConfig(services, nss),
                    new ParserConfig(services, nss),
                    null,
                    DefaultImmutableSet.<Taclet>nil()).problem();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    protected KeYLexerF getLexer(String s) {
        return new KeYLexerF(s,
                "No file. Call of parser from parser/" + getClass().getSimpleName());
    }

    protected KeYParserF getParser(String s) {
        return new KeYParserF(ParserMode.TERM, getLexer(s), services, nss);
    }

    public Term parseTerm(String s) {
        try {
            return getParser(s).term();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    public Term parseFormula(String s) {
        try {
            return getParser(s).formula();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    /**
     * Convert a {@link Term} into a {@link String}.
     *
     * @param t The {@link Term} that will be converted.
     */
    protected String printTerm(Term t) throws IOException {
        LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), services);
        lp.getNotationInfo().setHidePackagePrefix(false);
        lp.printTerm(t);
        return lp.toString();
    }

    /**
     * Remove whitespaces before executing
     * {@link junit.framework.TestCase#assertEquals(java.lang.String, java.lang.String)}.
     */
    protected void assertEqualsIgnoreWhitespaces(String expected, String actual) {
        assertEquals(expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""));
    }

    protected void assertEqualsIgnoreWhitespaces(String message, String expected, String actual) {
        assertEquals(message, expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""));
    }

    protected void verifyPrettyPrinting(String expectedPrettySyntax, Term expectedParseResult) throws IOException {
        // check whether pretty-printing the parsed term yields the original pretty syntax again
        String printedSyntax = printTerm(expectedParseResult);
        String message = "\nAssertion failed while pretty-printing a term:\n"
                + expectedParseResult
                + "\nExpected pretty-syntax is: \"" + expectedPrettySyntax
                + "\"\nBut pretty-printing resulted in: \"" + printedSyntax
                + "\"\n(whitespaces are ignored during comparison of the above strings)\n";
        assertEqualsIgnoreWhitespaces(message, expectedPrettySyntax, printedSyntax);
    }

    protected void verifyParsing(Term expectedParseResult, String expectedPrettySyntax) {
        // check whether parsing pretty-syntax produces the correct term
        Term parsedPrettySyntax = parseTerm(expectedPrettySyntax);
        String message = "\nAssertion failed while parsing pretty syntax. "
                + "Parsed string \"" + expectedPrettySyntax + "\", which results in term:\n"
                + parsedPrettySyntax + "\nBut expected parse result is:\n"
                + expectedParseResult + "\n";
        assertEquals(message, expectedParseResult, parsedPrettySyntax);
    }

    /**
     * Takes two different String representations for the same term and checks
     * whether they result in the same {@link Term} after parsing. Subsequently,
     * the {@link Term} is printed back to a {@link String} and compared with
     * the first argument. The first argument is expected to be in
     * pretty-syntax.
     *
     * @param prettySyntax {@link Term} representation in pretty-syntax.
     * @param verboseSyntax {@link Term} in verbose syntax.
     * @param optionalStringRepresentations Optionally, additional String
     * representations will be tested for correct parsing.
     * @throws IOException
     */
    protected void comparePrettySyntaxAgainstVerboseSyntax(String prettySyntax, String verboseSyntax,
            String... optionalStringRepresentations) throws IOException {
        Term expectedParseResult = parseTerm(verboseSyntax);
        compareStringRepresentationAgainstTermRepresentation(prettySyntax, expectedParseResult, optionalStringRepresentations);
    }

    /**
     * Takes a {@link String} and a {@link Term} and checks whether they can be
     * transformed into each other by the operations parsing and printing.
     *
     * @param prettySyntax Expected result after pretty-printing
     * {@code expectedParseResult}.
     * @param expectedParseResult Expected result after parsing
     * {@code expectedPrettySyntax}.
     * @param optionalStringRepresentations Optionally, additional String
     * representations will be tested for correct parsing.
     * @throws IOException
     */
    protected void compareStringRepresentationAgainstTermRepresentation(String prettySyntax, Term expectedParseResult,
            String... optionalStringRepresentations) throws IOException {

        verifyParsing(expectedParseResult, prettySyntax);
        verifyPrettyPrinting(prettySyntax, expectedParseResult);

        /*
         * Optionally, further string representations of the same term will be parsed here.
         */
        for (int i = 0; i < optionalStringRepresentations.length; i++) {
            assertEquals(expectedParseResult, parseTerm(optionalStringRepresentations[i]));
        }
    }

    protected abstract Services getServices();

}
