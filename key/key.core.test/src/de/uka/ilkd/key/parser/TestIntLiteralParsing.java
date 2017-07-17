package de.uka.ilkd.key.parser;

import org.junit.Test;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

public class TestIntLiteralParsing extends AbstractTestTermParser {

    public TestIntLiteralParsing() {
	super(TestIntLiteralParsing.class.getSimpleName());
    }
    
    @Override
    public Term parseTerm(String s) throws Exception {
        PositionedString p = new PositionedString(s);
        /*
         containerType and self variable are not relevant for the tests
         currently and can be changed if needed.
         */
        KeYJavaType containerType = services.getJavaInfo().getKeYJavaType("testTermParserHeap.A");
        ProgramVariable self = services.getJavaInfo().getCanonicalFieldProgramVariable("next", containerType);
        KeYJMLParser parser = new KeYJMLParser(p, getServices(), containerType, self,
                null, null, null, null);
        return parser.termexpression();
    }
    
    public SLExpression parseNumLiteral(String s) throws Exception {
        PositionedString p = new PositionedString(s);
        /*
         containerType and self variable are not relevant for the tests
         currently and can be changed if needed.
         */
        KeYJavaType containerType = services.getJavaInfo().getKeYJavaType("testTermParserHeap.A");
        ProgramVariable self = services.getJavaInfo().getCanonicalFieldProgramVariable("next", containerType);
        KeYJMLParser parser = new KeYJMLParser(p, getServices(), containerType, self,
                null, null, null, null);
        return parser.integerliteral();
    }
    
    static final String[] STRINGS = {
	//  	input					, 	expected output
	    "0xffff_ffff"				,	"Z(neglit(1(#)))",
	    "0x000"					,	"Z(0(#))",
	    "0x8000_0000"				,	"Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
	    "0x7fffffff"				,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "2147483647"				,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "-2147483648"				,	"javaUnaryMinusInt(Z(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
	    "0"						,	"Z(0(#))",
	    "-0"					,	"javaUnaryMinusInt(Z(0(#)))",
	    "00"					,	"Z(0(#))",
	    "017777777777"				,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "020000000000"				,	"Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
	    "01671003245"				,	"Z(3(3(9(4(2(8(9(4(2(#))))))))))",
	    "0b0"					,	"Z(0(#))",
	    "0b01111111111111111111111111111111"	,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "0b1000_0000_0000_0000_0000_0000_0000_0000"	,	"Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
	    "0b0100100100011101"			,	"Z(7(1(7(8(1(#))))))"
    };
    
    public void testIntLiteralParsing() throws Exception {
	Term t;
	String input, actual, expected, pretty;
	
	for (int i = 0; i < STRINGS.length / 2; i++) {
	    input = STRINGS[i*2];
	    expected = STRINGS[i*2 + 1];
	    
	    t = parseTerm(input);
	    actual = t.toString();
	    pretty = LogicPrinter.quickPrintTerm(t, services);
	    
	    //System.out.println("input: " + input + " term: " + actual + " expected: " + expected + " pretty: " + pretty);
	    assertEquals(expected, actual);
	    }
    }
    
    static final String[] LSTRINGS = {
	//  	input					, 	expected output
	    "0xffff_ffff_ffff_ffffL"			,	"Z(neglit(1(#)))",
	    "0x000l"					,	"Z(0(#))",
	    "0x8000_0000l"				,	"Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "0x7fffffffL"				,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "2147483647L"				,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "-2147483648l"				,	"javaUnaryMinusLong(Z(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
	    "0l"						,	"Z(0(#))",
	    "-0L"					,	"javaUnaryMinusInt(Z(0(#)))",
	    "00L"					,	"Z(0(#))",
	    "017777777777l"				,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "020000000000l"				,	"Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "01671003245L"				,	"Z(3(3(9(4(2(8(9(4(2(#))))))))))",
	    "0b0L"					,	"Z(0(#))",
	    "0b01111111111111111111111111111111L"	,	"Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "0b1000_0000_0000_0000_0000_0000_0000_0000l",	"Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
	    "0b0100100100011101L"			,	"Z(7(1(7(8(1(#))))))"
    };
    
    public void testLongLiteralParsing() throws Exception {
	Term t;
	String input, actual, expected, pretty;
	
	for (int i = 0; i < LSTRINGS.length / 2; i++) {
	    input = LSTRINGS[i*2];
	    expected = LSTRINGS[i*2 + 1];
	    
	    t = parseTerm(input);
	    actual = t.toString();
	    pretty = LogicPrinter.quickPrintTerm(t, services);
	    
	    //System.out.println("input: " + input + " term: " + actual + " expected: " + expected + " pretty: " + pretty);
	    assertEquals(expected, actual);		    
	}
    }
    
    private static final String[] INTRANGESTRINGS = {
	    "-2147483649",
	    "2147483648",
	    "0x100000000",
	    "0b100000000000000000000000000000000",
	    "040000000000"
    };
    
    public void testIntRange() throws Exception {
	for (String s : INTRANGESTRINGS) {
    	    try {
    	        parseTerm(s);
    	        fail();
    	    }
    	    catch (SLTranslationException e) {
    	        assertEquals("Number constant out of bounds", e.getMessage());
    	    }
	}
    }
    
    private static final String[] LONGRANGESTRINGS = {
	    "-9_223_372_036_854_775_809L",
	    "9223372036854775808L",
	    "0x10000000000000000l",
	    "0b10000000000000000000000000000000000000000000000000000000000000000l",
	    "020_0000_0000_0000_0000_0000L"
    };
    
    public void testLongRange() throws Exception {
	for (String s : LONGRANGESTRINGS) {
    	    try {
    	        parseTerm(s);
    	        fail();
    	    }
    	    catch (SLTranslationException e) {
    	        assertEquals("Number constant out of bounds", e.getMessage());
    	    }
	}
    }
}
