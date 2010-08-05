package de.uka.ilkd.key.smt.taclettranslation;

import java.util.HashMap;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;

/**
 * Translates a rewrite taclet to a formula.
 * 
 * 
 */
public class FindTacletTranslator extends AbstractTacletTranslator {


    static private final int ANTE = 0;
    static private final int SUCC = 1;
    /**
     * @param services
     */
    public FindTacletTranslator(Services services) {
	super(services);
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
	Term term = tb.imp(translateEqivalence(find, replace), add);
	return term;

    }
    
    private Term translateEqivalence(Term t1, Term t2){
	TermBuilder tb = TermBuilder.DF;
	return tb.equals(t1, t2);
    }
    
    private Term translateReplaceAndAddSequent(TacletGoalTemplate template, int type){
	
	TermBuilder tb = TermBuilder.DF;
	Sequent replace=null;
	if(template instanceof AntecSuccTacletGoalTemplate){
	    replace = ((AntecSuccTacletGoalTemplate)template).replaceWith();
	}

	Term add = template.sequent() != null ? translate(template.sequent())
		: STD_ADD;
	Term rep = replace == null ? STD_REPLACE : translate(replace);
	if (add == null)
	    add = STD_ADD;
	
	Term term = tb.or(rep, add);
	return term;
    }

    /**
     * Translates a RewriteTaclet to a formula.
     */
    public Term translateTaclet(Taclet t, ImmutableSet<Sort> sorts)
    	throws IllegalTacletException {
	

	

	usedVariables = new HashMap<String, LogicVariable>();

	FindTaclet findTaclet = (FindTaclet) t;
	TermBuilder tb = TermBuilder.DF;

	// the standard translation of the patterns.

	Term find = STD_FIND, assum = STD_ASSUM;

	// translate the find pattern.
	if (findTaclet.find() != null)
	    find = findTaclet.find();
	

	// translate the replace and add patterns of the taclet.
	ImmutableList<Term> list = ImmutableSLList.nil();

	for (TacletGoalTemplate template : findTaclet.goalTemplates()) {
	    
	    if(findTaclet instanceof AntecTaclet){
		list = list.append(translateReplaceAndAddSequent(template,ANTE));

	    }else if(findTaclet instanceof SuccTaclet){
		list = list.append(translateReplaceAndAddSequent(template,SUCC));

	    }else if(findTaclet instanceof RewriteTaclet){
		    if (findTaclet.find().sort().equals(Sort.FORMULA)) {
			list = list.append(translateReplaceAndAddFormula(
			         template, find));

		    } else {
			list = list.append(translateReplaceAndAddTerm(
			         template, find));

		    }
	    }else throw new IllegalTacletException("Not AntecTaclet, not SuccTaclet, not RewriteTaclet");
	    
	
	}


	if (findTaclet.ifSequent() != null) {
	    if ((assum = translate(findTaclet.ifSequent())) == null) {
		assum = STD_ASSUM;
	    }
	}
	
	
	if(findTaclet instanceof AntecTaclet || findTaclet instanceof SuccTaclet){
	    if(findTaclet instanceof AntecTaclet){
		find = tb.not(find); 
	    }
	    return tb.imp(tb.and(list),tb.or(find, assum));
	}


	return tb.imp(tb.and(list),assum);



    }

   
    




    @Override
    public void checkGoalTemplate(TacletGoalTemplate template)
	    throws IllegalTacletException {
	
	if(template instanceof RewriteTacletGoalTemplate)
	  checkTerm(((RewriteTacletGoalTemplate) template).replaceWith());
	if(template instanceof AntecSuccTacletGoalTemplate){
	    AntecSuccTacletGoalTemplate temp = (AntecSuccTacletGoalTemplate) template;
	    checkSequent(temp.replaceWith());
	}
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
	if (!(t instanceof FindTaclet)) {
	    throw new IllegalTacletException("Not a instance of "
		    + FindTaclet.class.getName());
	}
	checkGeneralConditions(t);
	checkTerm(((FindTaclet) t).find());
    }

}

