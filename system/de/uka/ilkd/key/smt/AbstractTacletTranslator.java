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



import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;


public abstract class AbstractTacletTranslator implements TacletTranslator {

    
    
    /** Translates a sequent to a term by using the following translations rules:
     * T ==> D is translated to: And(T)->Or(D).<br>
     * And(s): conjunction between all formulae in set s.
     * Or(s): disjunction between all formulae in set s.
     * @param s The sequent to be translated.
     * @return the resulting term of the translation or <code>null</code> if both antecedent and succendent are empty.
     */
    protected Term translate(Sequent s) {
        TermBuilder builder = new TermBuilder();
    
        
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
	if(checkAddRules(t)){return "The taclet has ddrules.";}
	if(t.getVariableConditions().hasNext()) {return "The taclet has variable conditions.";}
	return null;
    }
    
    /**
     * Checks whether the taclet has addrules. 
     * @param t taclet to be checked.
     * @return true, if the taclet has one or more addrules.
     */
    private boolean checkAddRules(Taclet t){
	for(TacletGoalTemplate template : t.goalTemplates())
	    if(template.rules().size() >0) return true;
	return false;
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
    
    
}
