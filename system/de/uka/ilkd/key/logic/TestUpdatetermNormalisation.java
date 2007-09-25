// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.io.File;

import junit.framework.TestCase;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;

/** 
 * class tests the term factory
 */
public class TestUpdatetermNormalisation extends TestCase { 

    public static final String testRules = System.getProperty("key.home")+
        File.separator+"examples"+
        File.separator+"_testcase"+File.separator+"updateterm";   

    private final HelperClassForTests helper = new HelperClassForTests();

    public ProofAggregate parse(File file) {
        return helper.parse(file);
    }
   

    public TestUpdatetermNormalisation(String name) {
	super(name);
    }

    public void setUp() {     	
    }

    private Term extractProblemTerm(Proof p) {
        return helper.extractProblemTerm(p);
    }

    public void testLocalVariableSort() {
	ProofAggregate proofList = parse
	    (new File(testRules+File.separator+"updatetermTest0.key"));
	Term t = extractProblemTerm(proofList.getFirstProof());
	assertTrue("Expected " + t.sub(1) + " but is " + t.sub(0),
		   t.sub(0).equals(t.sub(1))); 
    }
    
    public void testLocalVariableAttributeSort() {
    	ProofAggregate proofList = parse
	    (new File(testRules+File.separator+"updatetermTest1.key"));
	Term t = extractProblemTerm(proofList.getFirstProof());
	assertTrue("Expected " + t.sub(1) + " but is " + t.sub(0),
		   t.sub(0).equals(t.sub(1)));
    }

    public void testLocalVariableAttributeArraySort() {
    	ProofAggregate proofList = parse
	    (new File(testRules+File.separator+"updatetermTest2.key"));
	Term t = extractProblemTerm(proofList.getFirstProof());
	assertTrue("Expected " + t.sub(1) + " but is " + t.sub(0),
		   t.sub(0).equals(t.sub(1)));
    }

    public void testLocalVariableAttributeArrayShadowSort() {
    	ProofAggregate proofList = parse
	    (new File(testRules+File.separator+"updatetermTest3.key"));
	Term t = extractProblemTerm(proofList.getFirstProof());
	assertTrue("Expected " + t.sub(1) + " but is " + t.sub(0),
		   t.sub(0).equals(t.sub(1)));
    }
    
    public void testNoOrdering() {
        ProofAggregate proofList = parse
        (new File(testRules+File.separator+"updatetermTest4.key"));
    Term t = extractProblemTerm(proofList.getFirstProof());
    assertTrue("Expected " + t.sub(1) + " and " + t.sub(0) + " to be different",
           !t.sub(0).equals(t.sub(1)));
    }
    
}
