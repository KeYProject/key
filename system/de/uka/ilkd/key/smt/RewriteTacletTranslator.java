package de.uka.ilkd.key.smt;


import java.util.HashMap;
import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;

import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;

import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;


/** Translates a rewrite taclet to a formula. 
 * 
 *
 */
public class RewriteTacletTranslator extends AbstractTacletTranslator{

    private final Term STD_REPLACE,STD_ADD,STD_ASSUM,STD_FIND;
    

    

    
    public RewriteTacletTranslator(){
	TermBuilder tb = TermBuilder.DF;
	STD_REPLACE = tb.ff();
	STD_ADD = tb.ff();
	STD_ASSUM  = tb.ff();
	STD_FIND = tb.ff();
    }
    
    /** Translates the replace and add pattern of a goal template to: find=replace->add <br>
     * Use this method if you want to translate a taclet, where the find pattern is a term.
     * @param template contains the replace and add pattern that are to be translated.
     * @param find the find pattern of the taclet, already translated.
     * @return translation 
     */
    private Term translateReplaceAndAddTerm(RewriteTacletGoalTemplate template, Term find){
	TermBuilder tb = TermBuilder.DF;
	Term replace = template.replaceWith()!=null ? template.replaceWith() : STD_REPLACE;
	Term add     = template.sequent()!=null ? translate(template.sequent()) : STD_ADD;
	if(add == null) add = STD_ADD;
	if(replace == null) replace = STD_REPLACE;
	

	
	Term term = tb.imp(tb.equals(find, replace),add);
	return term;
    }
    
    /** Translates the replace and add pattern of a goal template to: (find<->replace)->add<br>
     * Use this method if you want to translate a taclet, where the find pattern is a formula.
     * @param template contains the replace and add pattern that are to be translated.
     * @param find the find pattern of the taclet, already translated.
     * @return translation 
     */
    private Term translateReplaceAndAddFormula(RewriteTacletGoalTemplate template, Term find){
	TermBuilder tb = TermBuilder.DF;
	Term replace = template.replaceWith()!=null ? template.replaceWith() : STD_REPLACE;
	Term add     = template.sequent()!=null ? translate(template.sequent()) : STD_ADD;
	if(add == null) add = STD_ADD;
	if(replace == null) replace = STD_REPLACE;
	Term term = tb.imp(tb.equiv(find,replace),
		           add);
	return term;
    }
    
     
    /**
     * Translates a RewriteTaclet to a formula.
     */
    public Term translate(Taclet t) {
	if(!(t instanceof RewriteTaclet)) throw new IllegalArgumentException("The given taclet is not of the type RewriteTaclet");
	String checkResult;
//	if((checkResult=checkGeneralConditions(t)) != null) throw new IllegalArgumentException(checkResult);
	usedVariables = new HashMap<String,LogicVariable>();
	
	RewriteTaclet rewriteTaclet = (RewriteTaclet)t;
	TermBuilder tb = TermBuilder.DF;
	
	//the standard translation of the patterns.
	
	Term find    = STD_FIND, 
	     assum   = STD_ASSUM;
	
	
	
	//translate the find pattern.
	if(rewriteTaclet.find() != null) find = rewriteTaclet.find();

	//translate the replace and add patterns of the taclet.
	ImmutableList<Term> list = ImmutableSLList.nil();
	
	for(TacletGoalTemplate template : rewriteTaclet.goalTemplates()){
	    if(rewriteTaclet.find().sort() == Sort.FORMULA)  {list = list.append(translateReplaceAndAddFormula((RewriteTacletGoalTemplate)template, find));}
	    else 					     {list = list.append(translateReplaceAndAddTerm((RewriteTacletGoalTemplate)template, find));}  
	}
	
		
	
	
	if(rewriteTaclet.ifSequent()!= null){
	    if((assum = translate(rewriteTaclet.ifSequent()))== null){
		assum = STD_ASSUM;}	    
	}
	


	
	Term term;
	term = tb.imp(tb.and(list),assum);

	//Rebuild the term to exchange schema variables with logic varibales.
	term = rebuildTerm(term);
	// Quantifie over all free variables.
	for(QuantifiableVariable qv : term.freeVars()){
	    term = tb.all(qv, term);
	}
	

	
	
	return term;
	
    }
    
    @Override
    protected Term changeTerm(Term term){
	TermBuilder tb = TermBuilder.DF;
	if(term.op() instanceof SortedSchemaVariable){
	    term = tb.var(getLogicVariable(term.op().name(),term.sort()));
	}
	return term;
    }
    
   
    

    
    @Override
    public String checkGoalTemplate(TacletGoalTemplate template){
	String res;
	if(!(template instanceof RewriteTacletGoalTemplate)) return "GoalTemplate not of type RewriteTacletGoalTemplate.";
	res = checkTerm(((RewriteTacletGoalTemplate)template).replaceWith()); 
	if(res != TRANSLATABLE) return res; 
	return TRANSLATABLE;
    }

    public String check(Taclet t) {
	if(! (t instanceof RewriteTaclet)) return "Not a instance of " + RewriteTaclet.class.getName();
	
	String res = checkTerm(((RewriteTaclet)t).find());	
	if(res != TRANSLATABLE) return res;
	
	return checkGeneralConditions(t);
    }

}
