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
import de.uka.ilkd.key.util.DefaultExceptionHandler;
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
                        "No file. Call of parser from parser/TestTermParser.java",
                        null),
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
                            "No file. Call of parser from parser/TestTermParser.java",
                            null),
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
                "No file. Call of parser from parser/" + getClass().getSimpleName(),
                new DefaultExceptionHandler());
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

    protected abstract Services getServices();

}
