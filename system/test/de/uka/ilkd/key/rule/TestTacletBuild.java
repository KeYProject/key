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



package de.uka.ilkd.key.rule;

import java.io.File;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.SuccTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletPrefixBuilder;
import de.uka.ilkd.key.util.HelperClassForTests;

/**
 * class tests the building of Taclets in TacletBuilders, especially the
 * checking if the SchemaVariables fulfill certain conditions. They must
 * not occur more than once in find and if taken as a whole. Is obviously
 * quite incomplete.
 */

public class TestTacletBuild extends TestCase {

    public static final Term[] NO_SUBTERMS = new Term[0];

   private TermFactory tf;

   private TermBuilder tb;

    public TestTacletBuild(String name) {
	super(name);
    }

    public void setUp() {
	TacletForTests.setStandardFile(TacletForTests.testRules);
	TacletForTests.parse();
	 tb = TacletForTests.services().getTermBuilder();
    tf = tb.tf();
    }

    public void test0() {
	SchemaVariable u=(SchemaVariable) 
	    TacletForTests.getVariables().lookup(new Name("u"));
	SchemaVariable v=(SchemaVariable) 
	    TacletForTests.getVariables().lookup(new Name("v"));
	Term b=tf.createTerm((SchemaVariable) 
	    TacletForTests.getVariables().lookup(new Name("b")), NO_SUBTERMS);
	Term t1=tb.ex((QuantifiableVariable)u, b);
	Term t2=tb.ex((QuantifiableVariable)v, b);
	RewriteTacletBuilder sb=new RewriteTacletBuilder();
	sb.setFind(t1);
	sb.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
					 ImmutableSLList.<Taclet>nil(),
					 t2));
	boolean thrown=false;
	try {
	    sb.getTaclet();
	} catch (RuntimeException e) {
	    thrown = true;
	}
	assertTrue("An exception should be thrown as there are different "
		   +"prefixes at different occurrences", thrown);
	sb.addVarsNotFreeIn(u, (SchemaVariable) b.op());
	sb.addVarsNotFreeIn(v, (SchemaVariable) b.op());
	sb.getTaclet();  //no exception is thrown here anymore
	
    }


    public void testUniquenessOfIfAndFindVarSVsInIfAndFind() {
	boolean thrown=false;
	SchemaVariable u=(SchemaVariable) 
	    TacletForTests.getVariables().lookup(new Name("u"));
	Term A=tf.createTerm
	    ((Function)TacletForTests.getFunctions().lookup(new Name("A")), 
	     NO_SUBTERMS);
	Term t1=tb.all((QuantifiableVariable)u, A);
	Sequent seq = Sequent.createSuccSequent
	    (Semisequent.EMPTY_SEMISEQUENT.insert
	     (0, new SequentFormula(t1)).semisequent());
	Term t2=tb.ex((QuantifiableVariable)u, A);
	SuccTacletBuilder sb=new SuccTacletBuilder();
	sb.setIfSequent(seq);
	sb.setFind(t2);
	try {
	    sb.getTaclet();
	} catch (IllegalArgumentException e) {
	    thrown=true;
	}
	assertTrue("An exception should be thrown as a bound SchemaVariable "+
		   "occurs more than once in the Taclets if and find", thrown);
    }


    public void testUniquenessOfIfAndFindVarSVBothInIf() {
	boolean thrown=false;
	SchemaVariable u=(SchemaVariable) 
	    TacletForTests.getVariables().lookup(new Name("u"));
	Term A=tf.createTerm
	    ((Function)TacletForTests.getFunctions().lookup(new Name("A")), 
	     NO_SUBTERMS);
	Term t1=tb.all( (QuantifiableVariable)u, A);
	Term t2=tb.ex((QuantifiableVariable)u, A);
	Sequent seq = Sequent.createSuccSequent
	    (Semisequent.EMPTY_SEMISEQUENT
	     .insert(0, new SequentFormula(t1)).semisequent()
	     .insert(1, new SequentFormula(t2)).semisequent());
	SuccTacletBuilder sb=new SuccTacletBuilder();
	sb.setIfSequent(seq);
	sb.setFind(A);
	try {
	    sb.getTaclet();
	} catch (IllegalArgumentException e) {
	    thrown=true;
	}
	assertTrue("An exception should be thrown as a bound SchemaVariable "
		   +"occurs more than once in the Taclets if and find", thrown);
    }



    public void testUniquenessOfIfAndFindVarSVsInFind() {
	boolean thrown=false;
	SchemaVariable u=(SchemaVariable) 
	    TacletForTests.getVariables().lookup(new Name("u"));
	Term A=tf.createTerm
	    ((Function)TacletForTests.getFunctions().lookup(new Name("A")), 
	     NO_SUBTERMS);
	Term t1=tb.all((QuantifiableVariable)u, A);
	SuccTacletBuilder sb=new SuccTacletBuilder();
	sb.setFind(tf.createTerm(Junctor.AND,t1,t1));
	try {
	    sb.getTaclet();
	} catch (IllegalArgumentException e) {
	    thrown=true;
	}
	assertTrue("An exception should be thrown as a bound SchemaVariable "+
		   "occurs more than once in the Taclets if and find", thrown);
    }

    private final HelperClassForTests helper = new HelperClassForTests();
    
    public static final String testRules = System.getProperty("key.home")+
        File.separator+"examples"+
        File.separator+"_testcase"+File.separator+"tacletprefix";
    
    public void testSchemavariablesInAddrulesRespectPrefix() {        
        try {
            helper.parseThrowException
            (new File(testRules+File.separator+
                    "schemaVarInAddruleRespectPrefix.key"));
        } catch (Throwable t) {
            assertTrue("Expected taclet prefix exception but was " + t,
                    t instanceof TacletPrefixBuilder.InvalidPrefixException);
            return;
        }
        fail("Expected an invalid prefix exception as the the addrule contains " +
        		"a schemavariable with wrong prefix.");
        
    }
}
