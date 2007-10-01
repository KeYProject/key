// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

import java.io.FileReader;
import java.io.IOException;

import org.apache.log4j.Logger;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SLListOfProgramVariable;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestRecoder2KeY extends TestCase {
	
	
	
    public TestRecoder2KeY(String name) {
	super(name);
    }

    private Recoder2KeY c2k;

    // some non sense java blocks with lots of statements and expressions
    private static String[] jblocks = new String[] {
	"{int j=7; int i;\n i=1; double d=0.4; float f=1.445; long l=123; \n "
	+"for (i=0, j=1; (i<42) && (i>0); i++, j--)\n"
	+" { i=13; j=1; } "
	+"while ((-i<7) || (i++==7--) | (--i==++7) ||(!true && false) ||"
	+" ('a'=='d') "
	+"|| (\"asd\"==\"as\"+\"d\") & (d==f) ^ (d/f+2>=f*d-f%d)|| (l<=~i)"
	+" || !(this==null) || ((this!=null) ? (8<<j<8>>i) : (7&5>8>>>7L)"
	+" || (7|5!=8^4)) && i+=j && i=j && i/=j && i%=j && i-=j && i*=j"
	+" && i<<=j && i>>=j && i>>>=j && i&=j && i^=j && i|=j) j=7;"
	+"}",

	"{"
	+"int j=7; int i;\n i=1;"
	+"do { j++; } while (i==1);"
	+"if (j==42) j=7; else {i=7; j=43;}"
	+";;"
	+"label0: j=42;"
	+"switch (j-i) {case 7: j=2; case 42: j=3; default: j=4; }"
	+"while (j==42) loop1:{ if (j==7) break; if (j==43) break loop1;"
	+"if (j==42) continue; if (j==41) continue loop1;}"
	+"if (j>42) return;"
	+"synchronized(null) { j=7; }"
	+"}",
	"{ int x = 1; {Boolean b;} }",
	"{"
	+"int[] a; a=new int[3]; a=new int[]{2,3,4}; int j=a[2]; j=a.length;"
	+"}"

    };


    private static String[] jclasses=new String[] {
	"class A1 { public A1() { }} ",
	"package qwe.rty; import uio.pas; import dfg.hjk.*; import java.util.*;"	
	+"public abstract class A implements Z{"
	+"static {d=3; Vector v = new Vector();}"
	+"public static int d;"
	+"A (int j) { d=5; }"
	+"public A (int j, float k) {this(j); d=5; }"
	+"private static final A[] b=new A[]{null}; "
	+"float f; Boolean s;"
	+"public void abc() {"
	+"Object z=new A(4, 5) { public int d=7; };"
	+"abc(); A a=(A)null; a=def(a); a=def(a).ghi(a).ghi(a);}"	
	+"{ int x = 1; {int i = \"\\\".length}\"; } }"
	+"protected A def(A a) {a=ghi(a); return new A(3);}"
	+"private synchronized A ghi(A a) { a=ghi(a); ghi(a); A a1=null; "
	+" a1=ghi(a1); a=def(a); return null;}"
	+"protected abstract int[] jkl(A a, int i);"
	+"protected Object o() {if (s instanceof Class) return s.class;}"
	+"}"
	+"interface Z { public int d=0; }"
	+"interface Z0 extends Z {}"
	+"class A1 extends A { public static A a=new A(4); "
	+"A1 (int j) {super(j);} }",
	"public class B extends Object {"
	+"class E  { public E(Class s) {super();} }"
	+"}",
	" class circ_A {   static int a = circ_B.b;   } "
	+"class circ_B {   static int b = circ_A.a;   }",
	" class circ2_A {   static final int a = circ2_B.b;   } " // This fails for an
	+"class circ2_B {   static final int b = circ2_A.a;   }",  // unpatched recoder library
	"class Cycle1 { void m(Cycle2 c) {} } "  // cyclic references as method arguments
	+"class Cycle2 { void m(Cycle1 c) {} }",
        "class EmptyConstr { EmptyConstr(); } "  // empty constructors for stubs 
    };

    /** removes blanks and line feeds from a given string*/
    private static String removeBlanks(String s) {
	StringBuffer sb=new StringBuffer();
	for (int i=0; i<s.length(); i++) {
	    if (!(s.charAt(i)==(' ')) && !(s.charAt(i)==('\n')))
		sb.append(s.charAt(i));
	}
	return sb.toString();
    }

    public void setUp() {
	c2k=new Recoder2KeY
	    (new Services(), new NamespaceSet());
    }

    public void tearDown() {
	c2k = null;
    }


    public void testReadBlockWithContext() {
	ProgramVariable pv = new LocationVariable
	    (new ProgramElementName("i"), new KeYJavaType(PrimitiveType.JAVA_INT));
	ListOfProgramVariable list = SLListOfProgramVariable.EMPTY_LIST.prepend(pv);	
	JavaBlock block = c2k.readBlock("{ i = 2; }", c2k.createContext(list));
	ProgramVariable prgVarCmp = (ProgramVariable)	    
	    ((Operator)((StatementBlock)block.program()).
			getStatementAt(0)).getChildAt(0);
	assertTrue("ProgramVariables should be the same ones.", 
		   prgVarCmp == pv);
    }

    /** test compares the pretty print results from recoder and KeY modulo 
     * blanks and line feeds
     */
    public void testJBlocks() {
	for (int i=0; i<jblocks.length; i++) {	    
	    String keyProg
		= removeBlanks(c2k.readBlockWithEmptyContext
			      (jblocks[i]).toString());
	    String recoderProg
		= removeBlanks(c2k.recoderBlock
			       (jblocks[i], 
				c2k.createEmptyContext())
			       .toSource());
	    assertEquals("Block :" + i + " rec:"+recoderProg+ "key:"+keyProg, 
			 recoderProg, keyProg);	
	}
    }

    private void testClass(String is) {
        try {
            c2k = new Recoder2KeY(TacletForTests.services(), new NamespaceSet());
            CompilationUnit cu = c2k.readCompilationUnit(is);
        } catch (RuntimeException e) {
            System.err.println("An error occured while parsing: '" + is + "'");
            throw e;
        }

    }

  
    /** test compares the pretty print results from recoder and KeY modulo 
     * blanks and line feeds
     */
    public void testJClasses() {
	for (int i=0; i<jclasses.length; i++) {
	    testClass(jclasses[i]);
	}
    }


    /** test compares the pretty print results from recoder and KeY modulo 
     * blanks and line feeds. Input is the Recoder2KeY.java file.
     * Not working: RECODER does not recognize imports
     */
    public void xtestFileInput() {
	char[] ch=new char[100000];
	int n=0;
	try {
	    FileReader fr=new FileReader
		("de/uka/ilkd/key/java/Recoder2KeY.java");
	    n=fr.read(ch);
	} catch (IOException e) {
	    System.err.println("Recoder2KeY.java not found");
	}
	String inputString=new String(ch,0,n);
	testClass(inputString);
	
    }

    public static void main(String[] args) {
	Services services = new Services ();
	Recoder2KeY c2k = new Recoder2KeY(services, new NamespaceSet());
	recoder.java.StatementBlock
	    jb = c2k.recoderBlock("{int len; int[] i = new int[] {0,1,2} ;  len = i.length;}",
				  c2k.createEmptyContext());
	System.out.println("Read: "+jb);
	recoder.java.StatementBlock block = (recoder.java.StatementBlock) jb;
	recoder.java.ProgramElement pe = block.getChildAt(2);
	System.out.println("Look at "+pe);
	//	de.uka.ilkd.key.java.CopyAssignment ca = ;
// 	System.out.println("Look at "+pe);

    }
}
