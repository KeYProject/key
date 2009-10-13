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



import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.taclettranslation.DefaultTacletSetTranslation;
import de.uka.ilkd.key.smt.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.smt.taclettranslation.RewriteTacletTranslator;
import de.uka.ilkd.key.smt.taclettranslation.TacletFormula;
import de.uka.ilkd.key.smt.taclettranslation.TacletSetTranslation;
import de.uka.ilkd.key.smt.taclettranslation.TacletTranslator;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import junit.framework.Assert;


public class TestTacletTranslation extends TestTaclet {
    
    
    
    
    protected void setUp(){
	parse();
    }
    

    
    
    /**
     * Searches for a taclet identified by its name.
     * @param name Name of the taclet
     * @return if sucessfull the taclet called 'name', otherwise null
     */
    private Taclet getTacletByName(String name){
	for(Taclet t: getTaclets()){
	    if(t.name().toString().equals(name)){
		return t;
	    }
	}
	return null;
    }
    
    public void testTranslateWhatYouGet(){

	TacletSetTranslation  translation = new DefaultTacletSetTranslation();
	translation.setTacletSet(getTaclets());
	translation.addHeuristic("smt_axiom_not_verified");
	/*
	System.out.println("\n\nTranslated: ");
	for(TacletFormula tf : translation.getTranslation()){
	    System.out.println(tf.getTaclet().name());
	}
	System.out.println("\n\nNot translated: ");
	for(TacletFormula tf : translation.getNotTranslated()){
	    System.out.println(tf.getTaclet().name()+"\n"+tf.getStatus()+"\n");
	}*/
	
	
    }
    
    /**
     * Taclets that should not be accepted. 
     */
    public void testBadExamples(){
	TacletSetTranslation  translation = new DefaultTacletSetTranslation();
	ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
	String [] tacletList = {
		"ex_bool",  // has a bad replace pattern: substitution
		//"testUninstantiatedSVCollector", // has a bad find pattern: diamond-operator
		//"TestCollisionResolving_coll_context", // has notFreeIn-Condtion:
		//"testParsingExplicitMethodBody", // has bad find pattern: box-operator
		"AND_literals_1", // has a bad replace pattern: meta-construct
		//"imp_left", // not a rewrite taclet
		//"TestMatchTaclet_whileright" // has variable conditions
		
	};
	
	String missing = "";
	for(String s : tacletList){
	    Taclet t = getTacletByName(s);
	    if(t == null) {missing += s+";";}
	    else          {set = set.add(t);} 
	}
	
	
	
	
	
	Assert.assertTrue("Some taclets have not been loaded: "+missing,tacletList.length == set.size());
		
	
	
	translation.setTacletSet(set);
	

	ImmutableList<TacletFormula> list = translation.getTranslation();
	String reason = "The following taclets were translated:\n";
	for(TacletFormula tf : list){
	    reason = reason + tf.getTaclet().name().toString();
	}
	
	Assert.assertTrue(reason,list.size() == 0);
	
	//for(TacletFormula tf : translation.getNotTranslated())
	  //  System.out.println(tf.getTaclet().name()+": "+ tf.getStatus());
	
	
	
    }
    
    /**
     * This is only a simple syntactical test to ensure that there is no change which
     * has a negative effect on the translation.
     */    
    public void testBooleanEqual() throws IllegalTacletException{
	Taclet t = getTacletByName("boolean_equal_2");
	Assert.assertTrue("Taclet boolean_equal_2 not found.", t!=null);

	TacletTranslator translator = new RewriteTacletTranslator();
	
	
	Term term = translator.translate(t);
	
	String s = "all({b1:boolean}all({b2:boolean}equiv(equiv(equals(b1,TRUE),equals(b2,TRUE)),equals(b1,b2))))";
	

	//printTerm(term,0);
	
	

	Assert.assertTrue("\n\nReference: "+s+"\nHypothese: "+ term.toString(),s.equals(term.toString()));

	//TODO: introduce mechanism to verify the translation.  
	
	
	// TODO: delete
	// Only for a very very quick test
	
	//System.out.println(LogicPrinter.quickPrintTerm(term,null));    
    }
    
    /**
     * This is only a simple syntactical test to ensure that there is no change which
     * has a negative effect on the translation.
     */
    public void testApplyEqBooleanRigid() throws IllegalTacletException{
	Taclet t = getTacletByName("apply_eq_boolean_rigid");
	Assert.assertTrue("Taclet apply_eq_boolean_rigid not found.", t!=null);

	TacletTranslator translator = new RewriteTacletTranslator();
	
	Term term = translator.translate(t);
	
	
	String s = "all({br:boolean}imp(not(equals(br,FALSE)),equals(br,TRUE)))";
	

	
	Assert.assertTrue("\n\nReference: "+s+"\nHypothese: "+ term.toString(),s.equals(term.toString()));
	
	
	//printTerm(term,0);

	//TODO: introduce mechanism to verify the translation.  
	
	// TODO: delete
	// Only for a very very quick test
	
	//System.out.println(LogicPrinter.quickPrintTerm(term,null));    
    }
    
    
 
    
    private void printTerm(Term term){
	System.out.println(LogicPrinter.quickPrintTerm(term,null)); 
    }
    
    public static void printTerm(Term t, int depth){
	System.out.println(depth + ": "+t.toString());
	
	//System.out.pritnln("VarsBoundHere: "+t.v);
	for(int i=0; i < t.arity(); i++){
	  printTerm(t.sub(i),depth+1);
	
	  
	}
	
	if(t.arity()== 0) {
	    System.out.println(depth+"Sort: "+t.sort());
	    System.out.println(depth+"FreeVar:"+t.freeVars().size());
	    System.out.println(depth+"Name:"+t.getClass().getName());
	   
	   
	    for(QuantifiableVariable qv : t.freeVars()){
		System.out.println(depth+"NameFreeVar:"+qv.toString()+" "+qv.getClass().getSimpleName());
	
	    }
	}
    }

    
    

    
    

    


}
