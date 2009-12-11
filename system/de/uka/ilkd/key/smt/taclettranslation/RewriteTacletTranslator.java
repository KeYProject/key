package de.uka.ilkd.key.smt.taclettranslation;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
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

    /**
     * @param services
     */
    public RewriteTacletTranslator(Services services) {
	super(services);
	// TODO Auto-generated constructor stub
    }

    private static final Term STD_REPLACE = TermBuilder.DF.ff(),
	    STD_ADD = TermBuilder.DF.ff(), STD_ASSUM = TermBuilder.DF.ff(),
	    STD_FIND = TermBuilder.DF.ff();
   



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
    private Term translateReplaceAndAddTerm(TacletGoalTemplate template,
	    Term find) {
	TermBuilder tb = TermBuilder.DF;
	Term replace = find;
	if(template instanceof RewriteTacletGoalTemplate){
	    replace = ((RewriteTacletGoalTemplate)template).replaceWith();
	}
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
	    TacletGoalTemplate template, Term find) {
	TermBuilder tb = TermBuilder.DF;
	Term replace = find;
	if(template instanceof RewriteTacletGoalTemplate){
	    replace = ((RewriteTacletGoalTemplate)template).replaceWith();
	}
		 
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
    public Term translateTaclet(Taclet t, ImmutableSet<Sort> sorts)
    	throws IllegalTacletException {
	

	

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
	    if (rewriteTaclet.find().sort().equals(Sort.FORMULA)) {
		list = list.append(translateReplaceAndAddFormula(
		         template, find));
	    } else {
		list = list.append(translateReplaceAndAddTerm(
		         template, find));
	    }
	}


	if (rewriteTaclet.ifSequent() != null) {
	    if ((assum = translate(rewriteTaclet.ifSequent())) == null) {
		assum = STD_ASSUM;
	    }
	}

	//Term term;
	//term = 
	
	return tb.imp(tb.and(list), assum);



    }

   
    




    @Override
    public void checkGoalTemplate(TacletGoalTemplate template)
	    throws IllegalTacletException {
	/*if (!(template instanceof RewriteTacletGoalTemplate)) {
	    throw new IllegalTacletException(
		    "GoalTemplate not of type RewriteTacletGoalTemplate: "+ template.getClass());
	}*/
	if(template instanceof RewriteTacletGoalTemplate)
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
    @Override
    protected void check(Taclet t) throws IllegalTacletException {
	if (!(t instanceof RewriteTaclet)) {
	    throw new IllegalTacletException("Not a instance of "
		    + RewriteTaclet.class.getName());
	}
	checkGeneralConditions(t);
	checkTerm(((RewriteTaclet) t).find());
    }

}
