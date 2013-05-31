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


package de.uka.ilkd.key.taclettranslation;



import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoFindTaclet;
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
public class DefaultTacletTranslator extends AbstractSkeletonGenerator {


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
     * @param polarity
     *            a value between -1 and 1. describes the expected polarity of
     *            the find clause (-1 antecedent, 0 both, +1 succedent)
     * @return translation
     */
    private Term translateReplaceAndAddFormula(
	    TacletGoalTemplate template, Term find, int polarity) {
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
	
	assert polarity == 0 || add == STD_ADD : 
	    "add() commands not allowed in polarity rules (syntactically forbidden)";

	Term term = tb.imp(translateEquivalence(find, replace, polarity), add);
	return term;

    }
    
    private Term translateEquivalence(Term find, Term replace, int polarity){
	TermBuilder tb = TermBuilder.DF;
	switch(polarity) {
	case 0: return tb.equals(find, replace);
	case 1: return tb.imp(replace, find);
	case -1: return tb.imp(find, replace);
	default: throw new IllegalArgumentException();
	}
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
    public Term translate(Taclet taclet)
    	throws IllegalTacletException {
	

	TermBuilder tb = TermBuilder.DF;

	// the standard translation of the patterns.

	Term find = STD_FIND, assum = STD_ASSUM;

	// translate the find pattern.
	if (taclet instanceof FindTaclet) {
	    FindTaclet findTaclet = (FindTaclet) taclet;
	    if (findTaclet.find() != null)
	        find = findTaclet.find();
	}

	// translate the replace and add patterns of the taclet.
	ImmutableList<Term> list = ImmutableSLList.nil();

	for (TacletGoalTemplate template : taclet.goalTemplates()) {
	    
	    if(taclet instanceof AntecTaclet){
		list = list.append(translateReplaceAndAddSequent(template,ANTE));

	    } else if(taclet instanceof SuccTaclet){
		list = list.append(translateReplaceAndAddSequent(template,SUCC));

	    } else if(taclet instanceof RewriteTaclet){
		    RewriteTaclet rwTaclet = (RewriteTaclet)taclet;
		    if (rwTaclet.find().sort().equals(Sort.FORMULA)) {
		        int polarity = getPolarity(rwTaclet);
			list = list.append(translateReplaceAndAddFormula(
			         template, find, polarity));

		    } else {
			list = list.append(translateReplaceAndAddTerm(
			         template, find));

		    }
	    } else if(taclet instanceof NoFindTaclet) {
	        list = list.append(translateReplaceAndAddSequent(template, SUCC));
	    } else {
	        throw new IllegalTacletException("Not AntecTaclet, not SuccTaclet, not RewriteTaclet, not NoFindTaclet");
	    }
	}
	if (taclet.ifSequent() != null) {
	    if ((assum = translate(taclet.ifSequent())) == null) {
		assum = STD_ASSUM;
	    }
	}
	
	
	if(taclet instanceof AntecTaclet || taclet instanceof SuccTaclet){
	    if(taclet instanceof AntecTaclet){
		find = tb.not(find); 
	    }
	    return tb.imp(tb.and(list),tb.or(find, assum));
	}
	return tb.imp(tb.and(list),assum);
    }

    private int getPolarity(RewriteTaclet rwTaclet) {
        int restr = rwTaclet.getApplicationRestriction();
        if((restr & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
            return -1;
        } else if((restr & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
            return +1;
        } else {
            return 0;
        }
    }
}

