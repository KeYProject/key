package de.uka.ilkd.key.smt.taclettranslation;

import java.util.HashMap;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
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
    public Term translate(Taclet t, ImmutableSet<Sort> sorts) throws IllegalTacletException {

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
	
	
	
	if(usedGenericSorts.size() > 1){
	    throw new IllegalTacletException("Can not translate taclets with more than one generic sort.");}
	
	ImmutableList<Term> genericTerms = ImmutableSLList.nil();
	// replace generic variables with logic variables.
	for(Sort sort : sorts){
	    
	    if(sort instanceof GenericSort){continue;}

	    for(GenericSort gs : usedGenericSorts){
		    genericTerms = genericTerms.append(instantiateGeneric(term, gs, sort));    
	
	    }  
	}

	// quantify the term
	ImmutableList<Term> genericTermsQuantified = ImmutableSLList.nil();
	if(genericTerms.size() > 0){
	    for(Term gt : genericTerms){
		gt = quantifyTerm(gt);
		genericTermsQuantified = genericTermsQuantified.append(gt); 
	    }
	    term = tb.and(genericTermsQuantified);
	    
	}else{
	    term = quantifyTerm(term);
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
	   if(!term.sort().equals(Sort.FORMULA)){
	    term = tb.all(qv, term);
	   }
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
