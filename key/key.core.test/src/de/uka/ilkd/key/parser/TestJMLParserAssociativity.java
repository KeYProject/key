package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;

/**
 * Test behaviour of {@link KeYJMLParser} for inputs in which braces are
 * omitted.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestJMLParserAssociativity extends AbstractTestTermParser {

    public TestJMLParserAssociativity() {
        super(TestJMLParserAssociativity.class.getSimpleName());
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

    /*
     * Test whether {@link KeYJMLParser} parses left-associatively for operators
     * that have same precedence.
     *
     * Example
     * 1 + 2 - 3 + 4 = ???                                  
     * Left-associative parsing: (((1 + 2) - 3) + 4) = 4
     * Right-associative parsing: (1 + (2 - (3 + 4))) = -4
     */
    public void testLeftAssociativity() throws Exception {

        // test */%
        String s1 = parseTerm("1 * 2 / 3 % 4 * 5 / 6 % 7").toString();
        String s2 = "javaMod(javaDivInt(javaMulInt(javaMod(javaDivInt(javaMulInt(Z(1(#)),Z(2(#))),Z(3(#))),Z(4(#))),Z(5(#))),Z(6(#))),Z(7(#)))";
        assertEquals(s1, s2);

        // test +-
        s1 = parseTerm("1 + 2 - 3 + 4 - 5").toString();
        s2 = "javaSubInt(javaAddInt(javaSubInt(javaAddInt(Z(1(#)),Z(2(#))),Z(3(#))),Z(4(#))),Z(5(#)))";
        assertEquals(s1, s2);

        // test ==
        s1 = parseTerm("1 == 1 == (2 == 2)").toString();
        s2 = "equiv(equals(Z(1(#)),Z(1(#))),equals(Z(2(#)),Z(2(#))))";
        assertEquals(s1, s2);

        // test & bitwise
        s1 = parseTerm("1 & 2 & 3").toString();
        s2 = "javaBitwiseAndInt(javaBitwiseAndInt(Z(1(#)),Z(2(#))),Z(3(#)))";
        assertEquals(s1, s2);

        // test & logical
        s1 = parseTerm("1 == 1 & 2 == 2 & 3 == 3").toString();
        s2 = "and(and(equals(Z(1(#)),Z(1(#))),equals(Z(2(#)),Z(2(#)))),equals(Z(3(#)),Z(3(#))))";
        assertEquals(s1, s2);

        // test | bitwise
        s1 = parseTerm("1 | 2 | 3").toString();
        s2 = "javaBitwiseOrInt(javaBitwiseOrInt(Z(1(#)),Z(2(#))),Z(3(#)))";
        assertEquals(s1, s2);

        // test | logical
        s1 = parseTerm("1 == 1 | 2 == 2 | 3 == 3").toString();
        s2 = "or(or(equals(Z(1(#)),Z(1(#))),equals(Z(2(#)),Z(2(#)))),equals(Z(3(#)),Z(3(#))))";
        assertEquals(s1, s2);

        // test ==>
        s1 = parseTerm("1 == 1 ==> 2 == 2 ==> 3 == 3").toString();
        s2 = "imp(equals(Z(1(#)),Z(1(#))),imp(equals(Z(2(#)),Z(2(#))),equals(Z(3(#)),Z(3(#)))))";
        assertEquals(s1, s2);
        
        // test <==
        s1 = parseTerm("1 == 1 <== 2 == 2 <== 3 == 3").toString();
        s2 = "imp(equals(Z(3(#)),Z(3(#))),imp(equals(Z(2(#)),Z(2(#))),equals(Z(1(#)),Z(1(#)))))";
        assertEquals(s1, s2);

        // test <==> and <=!=>
        s1 = parseTerm("1 == 1 <==> 2 == 2 <=!=> 3 == 3 <==> 4 == 4 <=!=> 5 == 5").toString();
        s2 = "not(equiv(equiv(not(equiv(equiv(equals(Z(1(#)),Z(1(#))),equals(Z(2(#)),Z(2(#)))),equals(Z(3(#)),Z(3(#))))),equals(Z(4(#)),Z(4(#)))),equals(Z(5(#)),Z(5(#)))))";
        assertEquals(s1, s2);
    }

}
