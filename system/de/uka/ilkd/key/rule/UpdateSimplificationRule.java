// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;

/**
 * Built in rule that starts the update simplifier on the sequent or
 * selected term. The rule is useful if one has changes the simultaneous
 * update simplifier settings. 
 */
public class UpdateSimplificationRule implements BuiltInRule {
    

    // container for old constrained formula and the one used to replace it
    static class ConstrainedFormulaContainer {

	private final ConstrainedFormula old;
	private final ConstrainedFormula replacement;
        private final boolean oldFormulaInAntecendent;
	
	public ConstrainedFormulaContainer
	    (ConstrainedFormula old, 
                    boolean oldFormulaInAntecendent,
                    ConstrainedFormula replacement) {
	    this.old = old;
            this.oldFormulaInAntecendent = oldFormulaInAntecendent;
	    this.replacement = replacement;
	}

	public ConstrainedFormula old() {
	    return old;
	}
        
        public boolean oldFormulaInAntecedent() {
            return oldFormulaInAntecendent;
        }

	public ConstrainedFormula replacement() {
	    return replacement;
	}

    }

    private static final ConstrainedFormulaContainer[] EMPTY_CONSTRAINEDFORMULA_ARRAY = 
        new ConstrainedFormulaContainer[0];

    public static UpdateSimplificationRule INSTANCE = new UpdateSimplificationRule();

    protected final Name name = new Name("Update Simplification");

    
    protected UpdateSimplificationRule() {
    }

    /** the rule is applied on the given goal using the
     * information of rule application. As applications of this rule kind may
     * not be successful in each case one has to ensure that the goal split is
     * done only iff the application was successful.
     * @param goal the goal that the rule application should refer to.
     * @param services the Services with the necessary information
     * about the java programs 
     * @param the rule application that is executed.
     */
    public ListOfGoal apply(Goal     goal, 
			    Services services, 
			    RuleApp  ruleApp) {

	ListOfGoal result = null;
	final ConstrainedFormulaContainer[] applicationResult;
	
	final PosInOccurrence pio = ruleApp.posInOccurrence();	    	
	final Sequent sequent = goal.sequent();
	if (pio == null) {		
	    applicationResult = applyOnSequent(sequent, 
		    			       goal.simplifier(),
		    			       services);	    
	} else {
	    applicationResult = applyOnTerm(goal.simplifier(), pio, services);
	}	


	if (applicationResult.length>0) { 
	    result = goal.split(1);
	    final Goal newGoal = result.head();	   
	    for (int i = 0, nr = applicationResult.length; i<nr; i++) {
		final ConstrainedFormulaContainer cfc = applicationResult[i];		
		final PosInOccurrence oldCFPIO = 
                    new PosInOccurrence(cfc.old(), PosInTerm.TOP_LEVEL,	
                            cfc.oldFormulaInAntecedent()); 	
		newGoal.changeFormula(cfc.replacement(), oldCFPIO);
	    }
	}
	return result;
    }



    private ConstrainedFormulaContainer[]
        applyOnSequent(Sequent seq, UpdateSimplifier sus,
                Services services) {			

	final LinkedList result = new LinkedList();
	
        applyOnSemisequent(seq.antecedent(), true, sus, services, result);
        applyOnSemisequent(seq.succedent(), false, sus, services, result);

	return (ConstrainedFormulaContainer[]) 
        result.toArray(new ConstrainedFormulaContainer[result.size()]);
    }

    private void applyOnSemisequent(Semisequent semiSeq, 
            boolean semiSeqIsAntecedent,
            UpdateSimplifier sus, 
            Services services, 
            final LinkedList result) {
        final IteratorOfConstrainedFormula it = semiSeq.iterator();	

        while (it.hasNext()) {
	    final ConstrainedFormula cf = it.next();
            final Term simplified = sus.simplify(cf.formula(), services);
	    if (simplified != cf.formula()) {
		result.add
		    (new ConstrainedFormulaContainer
			(cf,
                         semiSeqIsAntecedent,
			 new ConstrainedFormula(simplified, cf.constraint()))
			);		
	    }
	}
    }

    private ConstrainedFormulaContainer[] applyOnTerm
    (UpdateSimplifier sus, PosInOccurrence pio, Services services) {
	final ConstrainedFormulaContainer[] result;        
	
	ConstrainedFormula cf = pio.constrainedFormula();
	Term fml = cf.formula();

	Term simplified = sus.simplify(pio.subTerm(), services);
	if (simplified != fml) {
	    final ConstrainedFormula new_cf = new ConstrainedFormula
		(replace(fml, simplified, pio.posInTerm().iterator()), 
		 cf.constraint()); 
            result = new ConstrainedFormulaContainer[]
                    {new ConstrainedFormulaContainer(cf, pio.isInAntec(), 
                    new_cf)};
	} else {
	    result = EMPTY_CONSTRAINEDFORMULA_ARRAY;
        }

	return result;
    }

    public String displayName() {
	return toString();
    }
    
    /**
     * tests if the rule is applicable at the given position
     */
    public boolean isApplicable(Goal            goal, 
				PosInOccurrence pio,
				Constraint      userConstraint) {
	final Services services = goal.proof().getServices();
	if (pio != null) {
	    final Term fml = pio.subTerm ();
	    final Term simplified = goal.simplifier().simplify(fml, services);
	    if (!simplified.equals(fml)) {
		return true;
	    }
	} else { // this may be too slow; may be return true always
 	    final IteratorOfConstrainedFormula it = goal.sequent().iterator(); 	    
 	    while (it.hasNext()) {
 		ConstrainedFormula cf = it.next();
                final Term simplified = goal.simplifier().simplify(cf.formula(), services);
 		if (!simplified.equals(cf.formula())) {
 		    return true;
 		}
 	    }
	}
	return false;
    }

    public Name name() {
	return name;
    }


    private Term replace(Term term, Term with, IntIterator it) {	
	if (it.hasNext()) {	    
	    int sub=it.next();
	    Term[] subs=new Term[term.arity()];
	    final ArrayOfQuantifiableVariable[] vars = 
		new ArrayOfQuantifiableVariable[term.arity()];        
	    for (int i=0;i<term.arity();i++) {
		if (i!=sub) {
		    subs[i]=term.sub(i);
		} else {
		    subs[i]=replace(term.sub(i), with, it);
		}
		vars[i] = term.varsBoundHere(i);
	    }
	    
	    return TermFactory.DEFAULT.createTerm(term.op(), subs, vars,
						  term.javaBlock());	    
	}

	return with;
    }

    public String toString() {
	return name().toString();
    }
        
}
