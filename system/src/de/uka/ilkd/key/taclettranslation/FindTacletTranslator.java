// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.taclettranslation;



import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/**
 * Translates a rewrite taclet to a formula.
 * 
 * 
 */
public class FindTacletTranslator extends AbstractSkeletonGenerator {


    static private final int ANTE = 0;
    static private final int SUCC = 1;



    private static final Term STD_REPLACE = TermBuilder.DF.ff(),
    				 STD_ADD =     TermBuilder.DF.ff(), 
    				 STD_ASSUM = TermBuilder.DF.ff(),
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
	if (add == null){
	    add = STD_ADD;
	}
	if(rep == null){
	    rep = STD_REPLACE;
	}
	Term term = tb.or(rep, add);
	return term;
    }

    /**
     * Translates a RewriteTaclet to a formula.
     */
    @Override
    public Term translate(Taclet t)
    	throws IllegalTacletException {
	

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
}

