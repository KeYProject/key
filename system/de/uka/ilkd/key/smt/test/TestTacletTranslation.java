// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.test;

import java.io.File;


import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.BooleanSort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.proof.init.EnvInput;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JUnitTestProfile;
import de.uka.ilkd.key.proof.init.KeYFileForTests;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RewriteTaclet;


import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletForTests;



import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.Assert;
import junit.framework.TestCase;

/**
 * 
 *
 */
public class TestTacletTranslation extends TestCase {
    
    
 

    
    private static ImmutableSet<Taclet> taclets= null; 
    
    
    protected void setUp(){
	parse();
    }
    
    /** For any reason, this special initialization is needed, copyed from TacletForTests.
      */
    private static Profile profile = new JUnitTestProfile() {
        //we do not want normal standard rules, but ruleSetsDeclarations is needed for string library (HACK)
        public RuleCollection getStandardRules() {
            return new RuleCollection(
                            RuleSource.initRuleFile("ruleSetsDeclarations.key"), 
                            (ImmutableList)ImmutableSLList.nil());
        }
    };
    
    
    /**
     * Searches for a taclet identified by its name.
     * @param name Name of the taclet
     * @return if sucessfull the taclet called 'name', otherwise null
     */
    private Taclet getTacletByName(String name){
	for(Taclet t: taclets){
	    if(t.name().toString().equals(name)){
		return t;
	    }
	}
	return null;
    }
    
    public void testAll(){
	TacletSetTranslation  translation = new DefaultTacletSetTranslation();
	translation.setTacletSet(taclets);

	ImmutableList<TacletFormula> list = translation.getTranslation();
	
	System.out.println("Count: "+list.size());
	
	
	for(TacletFormula tf : list){
	    System.out.println(tf.getTaclet().toString());
	}
	
	
	/*
	for(Term term : list){
	    printTerm(term,0);
	}*/
	
    }
    
    /**
     * This is only a simple syntactical test to ensure that there is no change which
     * has a negative effect on the translation.
     */    
    public void testBooleanEqual(){
	Taclet t = getTacletByName("boolean_equal_2");
	Assert.assertTrue("Taclet boolean_equal_2 not found.", t!=null);

	TacletTranslator translator = new RewriteTacletTranslator();
	
	Term term = translator.translate(t);

	String s = "all({b1 (boolean term)}all({b2 (boolean term)}equiv(equiv(equals(b1,TRUE),equals(b2,TRUE)),equals(b1,b2))))";

	Assert.assertTrue(s.equals(term.toString()));

	//TODO: introduce mechanism to verify the translation.  
	
	
	// TODO: delete
	// Only for a very very quick test
	
	System.out.println(LogicPrinter.quickPrintTerm(term,null));    
    }
    
    /**
     * This is only a simple syntactical test to ensure that there is no change which
     * has a negative effect on the translation.
     */
    public void testApplyEqBooleanRigid(){
	Taclet t = getTacletByName("apply_eq_boolean_rigid");
	Assert.assertTrue("Taclet apply_eq_boolean_rigid not found.", t!=null);

	TacletTranslator translator = new RewriteTacletTranslator();
	
	Term term = translator.translate(t);
	
	
	String s = "all({br (boolean term)}imp(not(equals(br,FALSE)),equals(br,TRUE)))";
	

	
	Assert.assertTrue(s.equals(term.toString()));
	
	
	//printTerm(term,0);

	//TODO: introduce mechanism to verify the translation.  
	
	// TODO: delete
	// Only for a very very quick test
	
	System.out.println(LogicPrinter.quickPrintTerm(term,null));    
    }
    
    
    private void printTerm(Term term){
	System.out.println(LogicPrinter.quickPrintTerm(term,null)); 
    }
    
    private void printTerm(Term t, int depth){
	System.out.println(depth + ": "+t.toString());
	for(int i=0; i < t.arity(); i++){
	  printTerm(t.sub(i),depth+1);
	
	  
	}
	if(t.arity()== 0) {
	    System.out.println(depth+"Sort: "+t.sort());
	    System.out.println(depth+"FreeVar:"+t.freeVars().size());
	    for(QuantifiableVariable qv : t.freeVars()){
		System.out.println(depth+"NameFreeVar:"+qv.toString());
	    }
	}
    }

    
    
    /**
     * Loads taclets.
     */
    public static void parse(){
	if(taclets != null) return;
	 try{   
	        EnvInput envInput = new KeYFileForTests("Test", getProofFile());	
		ProblemInitializer pi = new ProblemInitializer(profile); 
		InitConfig ic = pi.prepare(envInput);
		taclets= ic.getTaclets();
	 }
	 catch(Exception e){
	     System.out.println(e);
	 }
	
	
    }
    
    
    /** 
     * @return returns the name of a prooffile in <code>folderPath</code>.
     */
    static private File getProofFile(){
	
	return new File(System.getProperty("key.home")+
	        File.separator+"examples"+
	        File.separator+"_testcase"+
	        File.separator+"testrules.key");
		
    }
    


}
