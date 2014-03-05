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


package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestSemisequent extends TestCase {
    
    private TermBuilder TB;
 
    private SequentFormula[] con;

    public TestSemisequent(String name) {
	super(name);
    }


    public void setUp() { 
       TB = TacletForTests.services().getTermBuilder();
       	Function p=new Function(new Name("p"),Sort.FORMULA,new Sort[]{});  
	Function q=new Function(new Name("q"),Sort.FORMULA,new Sort[]{});
	Function r=new Function(new Name("r"),Sort.FORMULA,new Sort[]{});

       	Function a=new Function(new Name("a"),Sort.FORMULA,new Sort[]{});  
	Function b=new Function(new Name("b"),Sort.FORMULA,new Sort[]{});
	Function c=new Function(new Name("c"),Sort.FORMULA,new Sort[]{});


	Term t_p=TB.func(p, new Term[]{});
	Term t_q=TB.func(q, new Term[]{});
	Term t_r=TB.func(r, new Term[]{});

 	Term t_a=TB.func(a, new Term[]{});
	Term t_b=TB.func(b, new Term[]{});
	Term t_c=TB.func(c, new Term[]{});

	
	con=new SequentFormula[7];
	con[0]=new SequentFormula(t_p);
	con[1]=new SequentFormula(t_q);
	con[2]=new SequentFormula(t_r);
	con[3]=new SequentFormula(t_r);
	con[4]=new SequentFormula(t_a);
	con[5]=new SequentFormula(t_b);
	con[6]=new SequentFormula(t_c);

	Sort s = new SortImpl(new Name("test"));
	Function f = new Function(new Name("f"), s, new Sort[]{});
 	Term t_f = TB.func(f, new Term[]{});
    }
       
    public void tearDown() {
        con = null;
    }
    
    private Semisequent extract(SemisequentChangeInfo semiCI) {
	return semiCI.semisequent();
    }

    public void testContains() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	SequentFormula eq2con0 = new SequentFormula(con[0].formula());
	assertTrue("Contains should test of identity and not equality.", !seq.contains(eq2con0));
    }

    public void testContainsEquals() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	SequentFormula eq2con0 = new SequentFormula(con[0].formula());
	assertTrue("Contains tests of equality and should find the formula.", seq.containsEqual(eq2con0));
    }

    public void testGet() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	assertSame(seq.get(0), con[0]);
	assertSame(seq.get(1), con[1]);
	
	try {
	    seq.get(2);
	} catch (IndexOutOfBoundsException iob) {
	    return;
	}
	fail();
    }


    public void testindexOf() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	seq=extract(seq.insert(2,con[2]));
	assertTrue("Semisequent has wrong size.", seq.size()==3);
	assertTrue("con[0] has wrong index in semisequent. Expected 0"+
		   " has "+ seq.indexOf(con[0]), seq.indexOf(con[0])==0); 
	assertTrue("con[1] has wrong index in semisequent. Expected 1"+ 
		   " has "+seq.indexOf(con[1]), seq.indexOf(con[1])==1);
	assertTrue("con[2] has wrong index in semisequent. Expected 2"+ 
		   " has "+seq.indexOf(con[2]), seq.indexOf(con[2])==2);	
    }

    public void testRemove() {

	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	seq=extract(seq.insert(2,con[2]));
	seq=extract(seq.remove(1));
	
	assertTrue("Semisequent has wrong size.", seq.size()==2);
	assertTrue("Semisequent contains deleted element.",!seq.contains(con[1]));
	assertTrue("con[1] has wrong index in semisequent",seq.indexOf(con[1])==-1);
	assertTrue("con[0] has wrong index in semisequent",seq.indexOf(con[0])==0);
	assertTrue("con[2] has wrong index in semisequent",seq.indexOf(con[2])==1);		
    }

    public void testReplace() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));	
	seq=extract(seq.replace(1,con[2]));
		
	
	assertTrue("Semisequent has wrong size.", seq.size()==2);
	assertTrue("Semisequent contains deleted element.",!seq.contains(con[1]));
	assertTrue("con[1] has wrong index in semisequent",seq.indexOf(con[1])==-1);
	assertTrue("con[0] has wrong index in semisequent",seq.indexOf(con[0])==0);
	assertTrue("con[2] has wrong index in semisequent",seq.indexOf(con[2])==1);		
    }

    public void testNoDuplicates() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	seq=extract(seq.insert(2,con[1]));
	
	assertTrue("Semisequent has duplicate",seq.size()==2);		
    }


    public void testImmutable() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	Semisequent old=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.insert(1,con[1]));
	old=seq;
	seq=extract(seq.insert(2,con[2]));
	
	assertTrue("Semisequent seems not to be immutable.",old.size()==2);
    }

    public void testUniqueEmpty() {
	Semisequent seq=Semisequent.EMPTY_SEMISEQUENT;
	seq=extract(seq.insert(0,con[0]));
	seq=extract(seq.remove(0));	
	assertSame("Semisequent is empty but not the EMPTY_SEMISEQUENT.",seq, Semisequent.EMPTY_SEMISEQUENT);

    }

    public void testEquals() {
	Semisequent seq1 = Semisequent.EMPTY_SEMISEQUENT;
	seq1 = extract(seq1.insert(0,con[0]));
	seq1 = extract(seq1.insert(0,con[1]));
	seq1 = extract(seq1.insert(0,con[2]));
	Semisequent seq2 = Semisequent.EMPTY_SEMISEQUENT;
	seq2 = extract(seq2.insert(0,con[0]));
	seq2 = extract(seq2.insert(0,con[1]));
	seq2 = extract(seq2.insert(0,con[2]));
	Semisequent seq3 = Semisequent.EMPTY_SEMISEQUENT;
	seq3 = extract(seq3.insert(0,con[0]));
	seq3 = extract(seq3.insert(0,con[1]));
	seq3 = extract(seq3.insert(0,con[3]));
	Semisequent seq4 = Semisequent.EMPTY_SEMISEQUENT;
	seq4 = extract(seq4.insert(0,con[0]));
	seq4 = extract(seq4.insert(0,con[2]));
	seq4 = extract(seq4.insert(0,con[1]));
	
	assertEquals("seq1=seq1",seq1,seq1);
	assertEquals("seq1=seq2",seq1,seq2);
	assertEquals("seq1=seq3",seq1,seq3);
	assertTrue("seq1!=seq4", ! seq1.equals(seq4));
    }

    public void testListInsert() {
	Semisequent origin   = extract(extract(extract(Semisequent.EMPTY_SEMISEQUENT.insertLast(con[0])).
	    insertLast(con[1])).insertLast(con[2]));

	Semisequent expected = extract(extract(extract(origin.insertLast(con[4])).insertLast(con[5])).
				       insertLast(con[6]));
	ImmutableList<SequentFormula> insertionList = ImmutableSLList.<SequentFormula>nil().
		    prepend(con[0]).prepend(con[1]).prepend(con[6]).prepend(con[5]).prepend(con[4]);
	Semisequent result = extract(origin.insert(origin.size(), insertionList));
	assertEquals("Both semisequents should be equal.", expected, result);
	
    }

    public void testListInsertInMid() {
	Semisequent origin = extract(extract(extract(Semisequent.EMPTY_SEMISEQUENT.insertLast(con[0])).
				     insertLast(con[1])).insertLast(con[2]));
 	Semisequent expected = extract(extract(extract(origin.insert(2, con[4])).insert(3, con[5])).insert(4, con[6]));
	ImmutableList<SequentFormula> insertionList = 
	    ImmutableSLList.<SequentFormula>nil().prepend(con[0]).prepend(con[1]).prepend(con[6]).prepend(con[5]).prepend(con[4]);
	Semisequent result = extract(origin.insert(origin.size()-1, insertionList));
	assertEquals("Both semisequents should be equal.", expected, result);
	
    }

    public void testListReplace() {
	// [p,q,r]
	Semisequent origin = extract(extract(extract(Semisequent.EMPTY_SEMISEQUENT.insertLast(con[0])).
	    insertLast(con[1])).insertLast(con[2]));
	// [p,q,a,b,c]
	Semisequent expected = 
	  extract(extract(extract(extract(origin.remove(2)).insertLast(con[4])).
			  insertLast(con[5])).insertLast(con[6]));
	// insert: [a,b,c,q,p]
	ImmutableList<SequentFormula> insertionList = ImmutableSLList.<SequentFormula>nil().
	  prepend(con[0]).prepend(con[1]).prepend(con[6]).prepend(con[5]).prepend(con[4]);

	SemisequentChangeInfo result = origin.replace(origin.size()-1, insertionList);

	assertEquals("SemisequentChangeInfo is corrupt due to wrong added formula list:",
		     ImmutableSLList.<SequentFormula>nil().prepend(con[4]).
		     prepend(con[5]).prepend(con[6]), result.addedFormulas());
	assertEquals("SemisequentChangeInfo is corrupt due to wrong removed formula list:",
		     ImmutableSLList.<SequentFormula>nil().prepend(con[2]),
		     result.removedFormulas());
	assertEquals("Both semisequents should be equal.", expected, extract(result));
	
    }

    public void testListReplaceAddRedundantList() {
	//[p,q]
 	Semisequent origin = extract(extract(Semisequent.EMPTY_SEMISEQUENT.insertLast(con[0])).
				     insertLast(con[1]));
	//[exp.: p,q,a,b,c,r]
 	Semisequent expected = extract(extract
				       (extract(extract(origin.insertLast(con[4])).
						insertLast(con[5])).insertLast(con[6])).insertLast(con[2]));
	// insert:[a,b,c,r,r,q,p]
 	ImmutableList<SequentFormula> insertionList = ImmutableSLList.<SequentFormula>nil().
 	    prepend(con[0]).prepend(con[1]).prepend(con[2]).prepend(con[3]).prepend(con[6]).prepend(con[5]).prepend(con[4]);
	
	SemisequentChangeInfo sci = origin.replace(origin.size(), insertionList);
	assertEquals("SemisequentChangeInfo is corrupt due to wrong added formula list:",
		     ImmutableSLList.<SequentFormula>nil().prepend(con[4]).prepend(con[5]).
		     prepend(con[6]).prepend(con[3]), sci.addedFormulas());
	assertEquals("SemisequentChangeInfo is corrupt due to wrong removed formula list:",
		     ImmutableSLList.<SequentFormula>nil(), sci.removedFormulas());
 	assertEquals("Both semisequents should be equal.", expected, extract(sci));	
    }

}
