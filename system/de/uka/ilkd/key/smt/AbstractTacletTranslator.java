// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// 
package de.uka.ilkd.key.smt;



import java.util.HashMap;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;


import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;


abstract class AbstractTacletTranslator implements TacletTranslator {

    protected final static TermFactory tf = TermFactory.DEFAULT;
    
    protected HashMap<String,LogicVariable> usedVariables = new HashMap<String,LogicVariable>();
    
    /** Translates a sequent to a term by using the following translations rules:
     * T ==> D is translated to: And(T)->Or(D).<br>
     * And(s): conjunction between all formulae in set s.
     * Or(s): disjunction between all formulae in set s.
     * @param s The sequent to be translated.
     * @return the resulting term of the translation or <code>null</code> if both antecedent and succendent are empty.
     */
    protected Term translate(Sequent s) {
        TermBuilder builder = TermBuilder.DF;
    
        
        ImmutableList<Term> ante = getFormulaeOfSemisequent(s.antecedent());
        ImmutableList<Term> succ = getFormulaeOfSemisequent(s.succedent());
        
         
        if(ante.size() == 0 && succ.size() == 0) return null;
        if(succ.size() == 0) return builder.not(builder.and(ante));
        if(ante.size() == 0) return builder.or(succ);
        
                

	return builder.imp(builder.and(ante),builder.or(succ));
    }
    
    /** Because the taclet translation follows a bottom up approach, there are taclets that can not be translated yet.
     * This method check whether there are general conditions that makes a translation impossible. 
     * @param t Taclet to be checked
     * @return if there is a problem the reason is returned, otherwise <code>null</code>
     */
    protected String checkGeneralConditions(Taclet t){
	
	
	if(t.getVariableConditions().hasNext()) {return "The taclet has variable conditions.";}
	if(t.varsNotFreeIn().hasNext()) {return "The taclet has \\notFreeIn conditions.";}
	//if(t.varshasNext()) {return "The taclet has ";}

	String res;
	
	res = checkGoalTemplates(t);
	if(res != TRANSLATABLE){ return res;}
	
	
	res = checkSequent(t.ifSequent());
	if(res != TRANSLATABLE){ return res;}	
	
	
	
	return TRANSLATABLE;
    }
    
    /**
     * Checks whether the taclet has addrules.<br>
     * @param t taclet to be checked.
     * @return <code>TRANSLATABLE</code> if there is no add rule, otherwise a string that is not empty.
     */
    private String checkGoalTemplates(Taclet t){
	for(TacletGoalTemplate template : t.goalTemplates()){
	    if(template.rules().size() >0) return "taclet has addrules.";
	    String res = checkSequent(template.sequent());
	    if(res != TRANSLATABLE) return res; 
	    res = checkGoalTemplate(template);
	    if(res !=TRANSLATABLE) return res;
	    
	}
	return TRANSLATABLE;
    }
    
    /**
     * Override this method if you want to check a goal template in a sub class.
     * @param template
     * @return  <code>TRANSLATABLE</code> if there is no add rule, otherwise a string that is not empty.
     */
    protected String checkGoalTemplate(TacletGoalTemplate template){return TRANSLATABLE;}
    
    /**
     * Checks the sequent by checking every term within in this sequent.
     * @param s
     *  @return <code>TRANSLATABLE</code> if the sequent is supported, otherwise a string that is not empty.
     */
    protected String checkSequent(Sequent s){
	String res;
	for(ConstrainedFormula cf : s){
	    if((res = checkTerm(cf.formula())) != TRANSLATABLE) return res;
	}
	return TRANSLATABLE;
    }
    
    
    /**
     * Checks whether a operator is supported. This method contains operators every taclet should support. 
     * Override this method if a special taclet should support more operators.
     * @param op the operator to be checked.
     * @return <code>TRANSLATABLE</code> if the operator is supported, otherwise a string that is not empty.
     */
    
    protected String checkOperator(Operator op){
	
	if((op instanceof Junctor) 
	   ||(op instanceof Equality) 
	   ||(op instanceof Quantifier)
	   ||(op instanceof RigidFunction)
	   // can't not be done by the typical 'instanceof' because TermSV and FormulaSV are not public. 
	   ||(op.getClass().getName().equals("de.uka.ilkd.key.logic.op.TermSV"))
	   ||(op.getClass().getName().equals("de.uka.ilkd.key.logic.op.FormulaSV"))
	  
	   //sss(op instanceof FormulaSV)//||
	   //||(op instanceof SortedSchemaVariable)
	   ) {return TRANSLATABLE;}
	return "The operator " + op.toString() + " is not supported. Class: "+op.getClass().getName();
    }
    
    
    
    /**
     * Checks the given term by checking the operator of the term and by checking the subterms. 
     * @param term the operator to be checked.
     * @return <code>TRANSLATABLE</code> if the term is supported, otherwise a string that is not empty.
     */    
    protected String checkTerm(Term term){
	
	String res = checkOperator(term.op());
	if(res != TRANSLATABLE) return res;
	for(int i=0; i < term.arity(); i++){
	    res = checkTerm(term.sub(i));
	    if(res != TRANSLATABLE) return res;
	}
	
	return TRANSLATABLE;
    }
    
    
    
    
    /**
     * Collects all formulae of a semisequent in a set.
     * @param s Semisequent.
     * @return A list of all formulae of the semisequent <code>s </code>.
     */
    private ImmutableList<Term> getFormulaeOfSemisequent(Semisequent s){
	ImmutableList<Term> terms = ImmutableSLList.nil();
	for(ConstrainedFormula cf: s){
	   terms = terms.append(cf.formula());
	}
	return terms;
	
    }
    
    /**
     * Use this method to rebuild the given term. The method splits the term in its single components and assemblies them. After every splitting step
     * the method calls <code>changeTerm</code>. This mechanism can be used to exchange subterms.
     * @param term the term to rebuild.
     * @return returns the new term.
     */
    protected Term rebuildTerm(Term term){
	ImmutableArray<QuantifiableVariable> variables[] = new  ImmutableArray[term.arity()];
	Term [] subTerms = new Term[term.arity()];
	for(int i=0; i < term.arity(); i++){
	   subTerms[i] = rebuildTerm(term.sub(i)); 
	   variables[i] = subTerms[i].varsBoundHere(i);
	}
	
	term = changeTerm(term);
	
	term = tf.createTerm(term.op(),subTerms,variables,JavaBlock.EMPTY_JAVABLOCK);
	return term;
    }
    
    /**
     * Returns a new logic variable with the given name and sort. If already a logic variable exists with the same name and sort this variable is returned
     * instead of a new logic variable.
     * @param name name of the logic variable.
     * @param sort sort of the logic variable.
     * @return logic variable with the given name and sort. 
     */
    protected LogicVariable getLogicVariable(Name name, Sort sort){
	LogicVariable l = usedVariables.get(name.toString());
	if(l== null){
	    l = new LogicVariable(name,sort);
	    usedVariables.put(name.toString(), l);
	}
	return l;
	
    }
    
    /**
     * Override this method if you want to change the term, i.e. exchanging schema variables with logic variables. See <code>rebuildTerm</code>.
     * @param term the term to be changed.
     * @return the new term.
     */
    protected Term changeTerm(Term term){
	return term;
    }
    
    
}
