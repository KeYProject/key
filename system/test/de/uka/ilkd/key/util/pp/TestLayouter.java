// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util.pp;

import java.io.IOException;

import junit.framework.TestCase;

/** Unit-Test the {@link Layouter} class. */

public class TestLayouter extends TestCase {

    /** A backend to remember the result in */
    StringBackend narrowBack;
    /** A backend to remember the result in */
    StringBackend wideBack;
    /** A backend to remember the result in */
    StringBackend sixBack;
    /** A layouter which breaks everything */
    MarkingBackend markBack;
    /** A layouter which breaks everything */
    Layouter narrow;
    /** A layouter which breaks nothing */
    Layouter wide;
    /** A layouter which breaks nothing */
    Layouter six;
    /** A layouter which breaks nothing */
    Layouter marking;

    int[] marks;
    int markPtr;

    public TestLayouter(String name) {
	super(name);
    }

    public void setUp() {
	narrowBack = new StringBackend(1);
	wideBack   = new StringBackend(10000);
	sixBack   = new StringBackend(6);
	markBack = new MarkingBackend(1);
	narrow = new Layouter(narrowBack,2);
	wide   = new Layouter(wideBack,2);
	six    = new Layouter(sixBack,2);
	marking= new Layouter(markBack,2);
	marks = new int[100];
	markPtr = 0;
    }

    

    class MarkingBackend extends StringBackend implements Backend {
	public MarkingBackend(int lineWidth) {
	    super(lineWidth);
	}

	public void mark(Object o) {
	    marks[markPtr++] = count();
	}
    }

    public void testNarrowConsistent() 
	throws UnbalancedBlocksException, IOException
    {
	narrow.beginC().print("A").beginC()
	    .print("B").brk(1,2)
	    .print("C").brk(2,3)
	    .print("D").end().print("E").end().close();
	assertEquals("break consistent","AB\n     C\n      DE",
		     narrowBack.getString());
    }

    public void testWideConsistent() 
	throws UnbalancedBlocksException, IOException
    {
	wide.beginC().print("A").beginC()
	    .print("B").brk(1,2)
	    .print("C").brk(2,3)
	    .print("D").end().print("E").end().close();
	assertEquals("no break consistent","AB C  DE",
		     wideBack.getString());
    }

    public void testNarrowInconsistent() 
	throws UnbalancedBlocksException, IOException
    {
	narrow.beginC().print("A").beginI()
	    .print("B").brk(1,2)
	    .print("C").brk(2,3)
	    .print("D").end().print("E").end().close();
	assertEquals("break inconsistent","AB\n     C\n      DE",
		     narrowBack.getString());
    }

    public void testWideInconsistent() 
	throws UnbalancedBlocksException, IOException
    {
	wide.beginC().print("A").beginI()
	    .print("B").brk(1,2)
	    .print("C").brk(2,3)
	    .print("D").end().print("E").end().close();
	assertEquals("no break inconsistent","AB C  DE",
		     wideBack.getString());
    }

    public void testSixInconsistent() 
	throws UnbalancedBlocksException, IOException
    {
	six.beginC().print("A").beginI()
	    .print("B").brk(1,2)
	    .print("C").brk(2,3)
	    .print("D").end().print("E").end().close();
	assertEquals("some breaks inconsistent","AB C\n      DE",
		     sixBack.getString());
    }

    public void testNarrowPre() 
	throws UnbalancedBlocksException, IOException
    {
	narrow.beginC().print("[")
	    .pre("A\nB\nC").print("]").end().close();
	assertEquals("preformatted","[A\n B\n C]",
		     narrowBack.getString());
	
    }

    public void testWidePre() 
	throws UnbalancedBlocksException, IOException
    {
	wide.beginC().print("[")
	    .pre("A\nB\nC").print("]").end().close();
	assertEquals("preformatted","[A\n B\n C]",
		     wideBack.getString());
	
    }

    public void testNarrowInd() 
	throws UnbalancedBlocksException, IOException
    {
	narrow.beginC().print("A").beginC()
	    .ind(1,2).print("B").brk(1,2)
	    .print("C").ind(3,4).print("D").brk(2,3)
	    .print("E").end().print("F").end().close();
	assertEquals("ind consistent","A    B\n     C D\n      EF",
		     narrowBack.getString());
    }

    public void testWideInd() 
	throws UnbalancedBlocksException, IOException
    {
	wide.beginC().print("A").beginC()
	    .ind(1,2).print("B").brk(1,2)
	    .print("C").ind(3,4).print("D").brk(2,3)
	    .print("E").end().print("F").end().close();
	assertEquals("ind consistent","A B C   D  EF",
		     wideBack.getString());
    }

    public void testMark() 
	throws UnbalancedBlocksException, IOException
    {
	marking.
	    beginC().mark(null) 
	    .print("A").mark(null) 
	    .beginC().mark(null) 
	    .print("B").mark(null) 
	    .brk(1,2).mark(null) 
	    .print("C").mark(null) 
	    .brk(2,3).mark(null) 
	    .print("D").mark(null) 
	    .end().mark(null) 
	    .print("E").mark(null) 
	    .end().mark(null) 
	    .close();
	assertEquals("break consistent","AB\n     C\n      DE",
		     markBack.getString());
	assertEquals("number marks",11,markPtr);
	assertEquals("marks pos 1",0,marks[0]);
	assertEquals("marks pos 2",1,marks[1]);
	assertEquals("marks pos 3",1,marks[2]);
	assertEquals("marks pos 4",2,marks[3]);
	assertEquals("marks pos 5",8,marks[4]);
	assertEquals("marks pos 6",9,marks[5]);
	assertEquals("marks pos 7",16,marks[6]);
	assertEquals("marks pos 8",17,marks[7]);
	assertEquals("marks pos 9",17,marks[8]);
	assertEquals("marks pos 10",18,marks[9]);
	assertEquals("marks pos 11",18,marks[10]);
    }
}

