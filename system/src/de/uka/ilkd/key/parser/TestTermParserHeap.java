package de.uka.ilkd.key.parser;

import junit.framework.TestCase;
import antlr.RecognitionException;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.DefaultExceptionHandler;

public class TestTermParserHeap extends TestCase {

    private static final boolean VERBOSE = false;
    private TermBuilder tb;
    private TermFactory tf;
    private NamespaceSet nss;
    private Recoder2KeY r2k;
    private Services serv;
    private Term storeTerm;

    public TestTermParserHeap() {
        if(serv != null) {
            return;
        }
        serv = TacletForTests.services ();
        tb = serv.getTermBuilder();
        tf = tb.tf();
        nss = serv.getNamespaces();
        r2k = new Recoder2KeY(serv, nss);
        r2k.parseSpecialClasses();      
    }

    
    public void testHeapAtExpressions() throws Exception {
        
        Term t1 = parseTerm("o.f@heap2");
        Term t2 = parseTerm("o.f@@abbr");
        
        try {
            Term t3 = parseTerm("o..f@heap");
            fail("Excepted to fail, but resulted in " + t3);
        } catch (RecognitionException e) {
            if(VERBOSE) {
                e.printStackTrace();
            }
        }
        
    }
    
    private KeYParserF stringTermParser(String s) throws AbbrevException {
        AbbrevMap map = new AbbrevMap();
        map.changeAbbrev(storeTerm, "abbr");
        return new KeYParserF(ParserMode.TERM,
                new KeYLexerF(s,
                        "No file. Call of parser from parser/TestTermParser.java",
                        new DefaultExceptionHandler()),
                r2k,
                serv,
                nss,
                map);
    }
    
    private Term parseTerm(String s) throws RecognitionException, AbbrevException {
        return stringTermParser(s).term();
    }

}
