package de.uka.ilkd.key.smt.taclettranslation;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.BoundedNumericalQuantifier;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableAdapter;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.op.WarySubstOp;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.TypeComparisionCondition;
import de.uka.ilkd.key.rule.conditions.TypeResolver;

/**
 * Translates a rewrite taclet to a formula.
 * 
 * 
 */
public class RewriteTacletTranslator extends AbstractTacletTranslator {

    private static final Term STD_REPLACE = TermBuilder.DF.ff(),
	    STD_ADD = TermBuilder.DF.ff(), STD_ASSUM = TermBuilder.DF.ff(),
	    STD_FIND = TermBuilder.DF.ff();
    private ImmutableSet<GenericSort> usedGenericSorts = DefaultImmutableSet.nil();

    public RewriteTacletTranslator() {

    }

    /**
     * Translates the replace and add pattern of a goal template to:
     * find=replace->add <br>
     * Use this method if you want to translate a taclet, where the find pattern
     * is a term.
     * 
     * @param template
     *            contains the replace and add pattern that are to be
     *            translated.
     * @param find
     *            the find pattern of the taclet, already translated.
     * @return translation
     */
    private Term translateReplaceAndAddTerm(RewriteTacletGoalTemplate template,
	    Term find) {
	TermBuilder tb = TermBuilder.DF;
	Term replace = template.replaceWith() != null ? template.replaceWith()
	        : STD_REPLACE;
	Term add = template.sequent() != null ? translate(template.sequent())
	        : STD_ADD;
	if (add == null)
	    add = STD_ADD;
	if (replace == null)
	    replace = STD_REPLACE;

	Term term = tb.imp(tb.equals(find, replace), add);
	return term;
    }

    /**
     * Translates the replace and add pattern of a goal template to:
     * (find<->replace)->add<br>
     * Use this method if you want to translate a taclet, where the find pattern
     * is a formula.
     * 
     * @param template
     *            contains the replace and add pattern that are to be
     *            translated.
     * @param find
     *            the find pattern of the taclet, already translated.
     * @return translation
     */
    private Term translateReplaceAndAddFormula(
	    RewriteTacletGoalTemplate template, Term find) {
	TermBuilder tb = TermBuilder.DF;
	Term replace = template.replaceWith() != null ? template.replaceWith()
	        : STD_REPLACE;
	Term add = template.sequent() != null ? translate(template.sequent())
	        : STD_ADD;
	if (add == null)
	    add = STD_ADD;
	if (replace == null)
	    replace = STD_REPLACE;
	Term term = tb.imp(tb.equiv(find, replace), add);
	return term;
    }

    /**
     * Translates a RewriteTaclet to a formula.
     */
    public Term translate(Taclet t, ImmutableSet<Sort> sorts)
    	throws IllegalTacletException {
	check(t);
	
	

	usedVariables = new HashMap<String, LogicVariable>();

	RewriteTaclet rewriteTaclet = (RewriteTaclet) t;
	TermBuilder tb = TermBuilder.DF;

	// the standard translation of the patterns.

	Term find = STD_FIND, assum = STD_ASSUM;

	// translate the find pattern.
	if (rewriteTaclet.find() != null)
	    find = rewriteTaclet.find();

	// translate the replace and add patterns of the taclet.
	ImmutableList<Term> list = ImmutableSLList.nil();

	for (TacletGoalTemplate template : rewriteTaclet.goalTemplates()) {
	    if (rewriteTaclet.find().sort() == Sort.FORMULA) {
		list = list.append(translateReplaceAndAddFormula(
		        (RewriteTacletGoalTemplate) template, find));
	    } else {
		list = list.append(translateReplaceAndAddTerm(
		        (RewriteTacletGoalTemplate) template, find));
	    }
	}

	if (rewriteTaclet.ifSequent() != null) {
	    if ((assum = translate(rewriteTaclet.ifSequent())) == null) {
		assum = STD_ASSUM;
	    }
	}

	Term term;
	term = tb.imp(tb.and(list), assum);

	// Rebuild the term to exchange schema variables with logic varibales.
	
	usedGenericSorts = DefaultImmutableSet.nil();
	term = rebuildTerm(term);
	
	
	
	Term genericTerm = instantiateGeneric(term, usedGenericSorts, sorts, t);
	
	term = genericTerm==null ? quantifyTerm(term) : genericTerm; 
	

	




	return term;

    }
    
    //TODO: !!!Find a better way to implement this method!!!!
    //TODO: Introduce a general method for testing the variable conditions.
    private boolean hasNotTheSameCondtion(Iterator<VariableCondition> it,
	    GenericSort [] gs){
	while(it.hasNext()){
	    VariableCondition vc = it.next();
	    
	    if(vc instanceof TypeComparisionCondition){
		TypeComparisionCondition t1  = ((TypeComparisionCondition)vc);
		 
		 
		
		TypeComparisionCondition t2 = new TypeComparisionCondition(
			TypeResolver.createGenericSortResolver(gs[1]),
			TypeResolver.createGenericSortResolver(gs[0]),
			TypeComparisionCondition.NOT_SAME);
		
		TypeComparisionCondition t3 = new TypeComparisionCondition(
			TypeResolver.createGenericSortResolver(gs[0]),
			TypeResolver.createGenericSortResolver(gs[1]),
			TypeComparisionCondition.NOT_SAME);
		
		
		
		if(t1.toString().equals(t3.toString())) return true;
		if(t1.toString().equals(t2.toString())) return true;
		
	
		
	    }
	}
	return false;
    }
    
    /**
     * Tests sort of its instantiation ability.
     * @param sort sort to be tested.
     * @return <code>true</code> if can be instantiated,
     *  otherwise <code>false</code>
     */
    private boolean doInstantiation(Sort sort){
	return !((sort instanceof GenericSort) || (sort.equals(Sort.ANY)));
    }
    

    /**
     * Instantiates generic variables of the term. 
     * It instantiates the variables using
     * all possibilities. This method supports two different 
     * generic variables and the following variable conditions:
     * - \not\same(G,H)
     * @param term the term to be instantiated.
     * @param genericSorts the generic sorts that should be replaced.
     * @param sorts the instantiations
     * @param t the current taclet, that is being translated.
     * @return returns a new term, where all generic variables
     * are instantiated.
     * @throws IllegalTacletException
     */
    private Term instantiateGeneric(Term term, 
	    ImmutableSet<GenericSort> genericSorts, ImmutableSet<Sort> sorts, Taclet t) 
	    throws IllegalTacletException{
	if(genericSorts.size() == 0){return null;}
	if(usedGenericSorts.size() > 2){
	    throw new 
	    IllegalTacletException("Can not translate taclets with " +
	    		"more than two generic sorts.");}
	
	ImmutableList<Term> genericTerms = ImmutableSLList.nil();
	
	GenericSort gs [] = new GenericSort[2];
	int i=0;
	for(GenericSort sort : genericSorts){
	    gs[i]= sort;
	    i++;
	}

	// instantiate the first generic variable
	for(Sort sort1 : sorts){
	    if(!doInstantiation(sort1)){continue;}
	  
	    Term temp = instantiateGeneric(term, gs[0], sort1);

	    if(temp == null){continue;}
	    
	    //instantiate the second generic variable
	    if(genericSorts.size() == 2){
		int instCount =0;
		
		for(Sort sort2 : sorts){

		   if(!(hasNotTheSameCondtion(t.getVariableConditions(),gs) && 
			   sort1.equals(sort2)) && 
			   doInstantiation(sort2)){
	
		            Term temp2 = instantiateGeneric(temp,gs[1],sort2);
		       	    if(temp2 !=null){
		       		instCount++;
		       		genericTerms = genericTerms.append(temp2);
		       	    }
		       	 
			} 
		    
		}
		if(instCount == 0){
		    throw new 
		    IllegalTacletException("Can not instantiate generic variables" +
			" because there are not enough different sorts.");
		}
	
	    }else{
		genericTerms = genericTerms.append(temp);
	    }
	    
	 
	}
	
	if(genericTerms.size() == 0){
		throw new 
		IllegalTacletException("Can not instantiate generic variables" +
		" because there are not enough different sorts.");
	} 
	

	// quantify the term
	ImmutableList<Term> genericTermsQuantified = ImmutableSLList.nil();
	if(genericTerms.size() > 0){
	     for(Term gt : genericTerms){
		genericTermsQuantified = genericTermsQuantified.append(quantifyTerm(gt)); 
		
	    }
	    term = TermBuilder.DF.and(genericTermsQuantified);
	    
	}
	return term;
    }
    
    
    /**
     * Quantifies a term, i.d. every free variable is bounded by a allquantor. 
     * @param term the term to be quantify.
     * @return the quantified term.
     */
    private Term quantifyTerm(Term term){
	TermBuilder tb = TermBuilder.DF;
	// Quantify over all free variables.
	for (QuantifiableVariable qv : term.freeVars()) {
	  // if(!term.sort().equals(Sort.FORMULA)){
	    term = tb.all(qv, term);
	  // }
	}
	return term;
    }

    @Override
    protected Term changeTerm(Term term) {
	
	
	TermBuilder tb = TermBuilder.DF;


		
	if(term.op() instanceof SortedSchemaVariable) {
	    if(term.sort().equals(Sort.FORMULA)){
		
	//	term = tb.var(getLogicVariable(term.op().name(),Sort.FORMULA));
		//term = tb.var(getLogicVariable(term.op().name(),term.sort()));
	    }else{
		
		term = tb.var(getLogicVariable(term.op().name(), term.sort()));
	    }
	    
	}
	if(term.sort() instanceof GenericSort){
	    usedGenericSorts  = usedGenericSorts.add((GenericSort) term.sort());   
	}
	return term;
    }

    @Override
    public void checkGoalTemplate(TacletGoalTemplate template)
	    throws IllegalTacletException {
	if (!(template instanceof RewriteTacletGoalTemplate)) {
	    throw new IllegalTacletException(
		    "GoalTemplate not of type RewriteTacletGoalTemplate.");
	}
	checkTerm(((RewriteTacletGoalTemplate) template).replaceWith());

    }

    /**
     * Checks the given taclet whether it can be translated.
     * 
     * @param t
     *            taclet to check.
     * @throws IllegalTacletException
     *             if the taclet can not be translated.
     */
    private void check(Taclet t) throws IllegalTacletException {
	if (!(t instanceof RewriteTaclet)) {
	    throw new IllegalTacletException("Not a instance of "
		    + RewriteTaclet.class.getName());
	}
	checkGeneralConditions(t);
	checkTerm(((RewriteTaclet) t).find());
    }

}
