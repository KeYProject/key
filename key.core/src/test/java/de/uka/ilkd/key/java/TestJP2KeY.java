/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.Collections;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

public class TestJP2KeY {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestJP2KeY.class);
    private static JavaService c2k;

    // some nonsense java blocks with lots of statements and expressions
    private static final String[] JAVA_BLOCKS = new String[] {
        """
                {
                    int j = 7;
                    int i;
                    i=1;
                    byte d = 0;
                    short f = 1;
                    long l = 123;
                    for (i=0, j=1; (i<42) && (i>0); i++, j--) { i=13; j=1; }
                    while ((-i<7) || (i++==7--) | (--i==++7) ||(!true && false) || ('a'=='d')\s
                    || ("asd"=="as"+"d") & (d==f) ^ (d/f+2>=f*d-f%d)|| (l<=~i)\s
                    || !(this==null) || ((this!=null) ? (8<<j<8>>i) : (7&5>8>>>7L)\s
                    || (7|5!=8^4)) && (i+=j) && (i=j) && (i/=j) && (i%=j) && (i-=j) && (i*=j)\s
                    && (i<<=j) && (i>>=j) && (i >>>= j) && (i &= j) && (i ^= j) && (i |= j))
                        j=7;
                 }
                """,

        """
                {
                    int j=7; int i;
                    i=1;do { j++; } while (i==1);if (j==42) j=7; else {i=7; j=43;};
                    ;
                    label0: j=42;
                    switch (j-i) {case 7: j=2; case 42: j=3; default: j=4; }
                    while (j==42) loop1:{ if (j==7) break; if (j==43) break loop1;
                    if (j==42) continue; if (j==41) continue loop1;}
                    if (j>42) return;synchronized(null) { j=7; }
                }
                """,
        "{ int x = 1; {java.util.List l;} }",
        "{int[] a; a=new int[3]; a=new int[]{2,3,4}; int j=a[2]; j=a.length;}"
    };


    private static final String[] JAVA_CLASSES = new String[] {
        "class A1 { public A1() { }} ",
        """
                package qwe.rty;
                import qwe.rty.A;
                import dfg.hjk.*;
                import java.util.*;
                public abstract class A implements Z {
                    static { d=3; Object v = new Object();}
                    public static int d;A (int j) { d=5; }
                    public A (int j, long k) {this(j); d=5; }
                    private static final A[] b=new A[]{null};
                    long f;
                    java.util.List s;
                    public void abc() {
                        Object z=new A(4, 5) { public int d=7; };
                        abc(); A a=(A)null;
                        a=def(a); a=def(a).ghi(a).ghi(a);
                    }

                    { int x = 1; {int i = "\\".length}"; } }
                    protected A def(A a) {a=ghi(a); return new A(3);}
                    private synchronized A ghi(A a) { a=ghi(a); ghi(a); A a1=null;  a1=ghi(a1); a=def(a); return null;}
                    protected abstract int[] jkl(A a, int i);
                    protected Object o() {if (s instanceof Cloneable) return A.class;}}
                    interface Z { public int d=0; }
                    interface Z0 extends Z {}
                    class A1 extends A { public static A a=new A(4); A1 (int j) {super(j);}
                }
                """,

        "public class B extends Object {class E  { public E(Object s) {super();} }}",
        " class circ_A {   static int a = circ_B.b;   } class circ_B {   static int b = circ_A.a;   }",
        " class circ2_A {   static final int a = circ2_B.b;   } " +
            "class circ2_B {   static final int b = circ2_A.a;   }",
        "class Cycle1 { void m(Cycle2 c) {} } class Cycle2 { void m(Cycle1 c) {} }",
        "class EmptyConstr { EmptyConstr(); } "
    };

    /**
     * removes blanks and line feeds from a given string
     */
    private static String removeBlanks(String s) {
        return s.replaceAll("\\s+", "");
    }

    @BeforeEach
    public void setUp() throws URISyntaxException, IOException {
        if (c2k == null) {
            c2k = TacletForTests.services().getJavaService();
            c2k.parseSpecialClasses(null);
        }
    }


    @Test
    public void testReadBlockWithContext() {
        IProgramVariable pv = new LocationVariable(new ProgramElementName("i"),
            TacletForTests.services().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT));
        var list = Collections.singletonList(pv);
        JavaBlock block = c2k.readBlock("{ i = 2; }", c2k.createContext(list), null);
        ProgramVariable prgVarCmp =
            (ProgramVariable) ((Operator) ((StatementBlock) block.program()).getStatementAt(0))
                    .getChildAt(0);
        assertSame(prgVarCmp, pv, "ProgramVariables should be the same ones.");
    }

    /**
     * test compares the pretty print results from recoder and KeY modulo blanks and line feeds
     */
    @TestFactory
    public Stream<DynamicTest> testJBlocks() {
        return Arrays.stream(JAVA_BLOCKS).map(it -> DynamicTest.dynamicTest(it, () -> {
            String keyProg = removeBlanks(c2k.readBlockWithEmptyContext(it, null).toString());
            String recoderProg =
                removeBlanks(c2k.parseBlock(it, c2k.createEmptyContext()).toString());
            assertEquals(recoderProg, keyProg);
        }));
    }

    private void testClass(String is) {
        try {
            c2k.readCompilationUnit(is);
        } catch (RuntimeException e) {
            LOGGER.error("An error occurred while parsing:", e);
            throw e;
        }
    }

    /**
     * test compares the pretty print results from recoder and KeY modulo blanks and line feeds
     */
    @TestFactory
    public Stream<DynamicTest> testJClasses() {
        return Arrays.stream(JAVA_CLASSES)
                .map(it -> DynamicTest.dynamicTest(it, () -> testClass(it)));
    }
}
