package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/** This class behaves almost the same as {@code SmtLibTranslator} but it semantically weakens the 
 * the output formula (a little bit) because otherwise the SMT solvers are not able to find models,
 * i.e. the don't output the result "sat" for formulas that a obviously satisfiable. Consider
 * the following example
 * <p>
 * :notes "Assumptions for sort predicates:"<br>
   :assumption (forall (?tvar_12 Int) (implies (type_of_jint_0_1 ?tvar_12) (type_of_int_3_4 ?tvar_12)))<br>
    <br>
   :notes "The formula to proof:"<br>
   :formula (and (= x_5 0) (= self_8 null))
    <\p>
    <p>Z3 and Yices are not able to find a model for the formula. If the quantified formula in the 
    assumption is removed, then they are capable to find a model. If the formula gets a little
    bit more complicated then also CVC3 cannot find a model.
    <p>The implementation of this class removes quantified formulas in the axiomatization of
    the type system (or replaces them by some instances of the formula). The consequence is that verification
    remains sound, but bug-detection via SMT-solvers may find models that don't respect the type
    system. These cases should, however, be very rare.
    @author gladisch
    */
public class SmtLibTranslatorWeaker extends SmtLibTranslator {

    /** @see {@link SmtLibTranslatorWeaker} (Description of the class) */
    public SmtLibTranslatorWeaker(Sequent sequent, Services services) {
	super(sequent, services);
    }

    /** @see {@link SmtLibTranslatorWeaker} (Description of the class) */
    public SmtLibTranslatorWeaker(Services s) {
	super(s);
    }

    /**
     * build the formulas, that make sure, special functions keep
     * typing
     * @return ArrayList of formulas, assuring the assumption.
     */
    protected ArrayList<StringBuffer> getSpecialSortPredicates(Services services) throws IllegalFormulaException{
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
	return toReturn;
    }
    
    /**Get the expression for that defines the typepredicates for sort hierarchy.
     * Also the null type is added to the formula if used before.
     * @return The same as the overwritten method from the parent class
     * but formulas with quantifiers are not created.
     */
    protected ArrayList<StringBuffer> getSortHierarchyPredicates() {
	SortHierarchy sh = this.buildSortHierarchy();
	ArrayList<StringBuffer> toReturn = new ArrayList<StringBuffer>();
/*	
	// add the typepredicates for functions.
	HashMap<StringBuffer, ArrayList<StringBuffer>> predMap = sh
		.getDirectSuperSortPredicate();
	for (StringBuffer leftPred : predMap.keySet()) {
	    StringBuffer form = new StringBuffer();
	    for (StringBuffer rightPred : predMap.get(leftPred)) {
		StringBuffer var = this.translateLogicalVar(new StringBuffer("tvar"));
		ArrayList<StringBuffer> varlist = new ArrayList<StringBuffer>();
		varlist.add(var);
		StringBuffer leftForm = this.translatePredicate(leftPred,varlist);

		StringBuffer rightForm = this.translatePredicate(rightPred,varlist);

		form = this.translateLogicalImply(leftForm, rightForm);
		if (this.isMultiSorted()) {
		    form = this.translateLogicalAll(var, this.standardSort,form);
		} else {
		    form = this.translateLogicalAll(var, this.getIntegerSort(),form);
		}
	    }
	    if (form.length() > 0) {
		toReturn.add(form);
	    }
	}
*/
	// add the typepredicates for null
	if (this.nullUsed) {
	    for (StringBuffer s : this.typePredicates.values()) {
		ArrayList<StringBuffer> argList = new ArrayList<StringBuffer>();
		argList.add(this.nullString);
		StringBuffer toAdd = this.translatePredicate(s, argList);
		toReturn.add(toAdd);
	    }
	}

	return toReturn;
    }

    /**
     * Get the type predicate definition for a given function.
     * If the result type is of some int type, empty StringBuffer is returned.
     * 
     * @param funName the name of the function.
     * @param sorts the sorts, the function is defined for. 
     * 		Last element is the return type.
     */
    protected StringBuffer getSingleFunctionDef(StringBuffer funName,
	    ArrayList<Sort> sorts) {
	StringBuffer toReturn = new StringBuffer();
	return toReturn;
    }
    
//    /** Returning false should result in untyped quantification. However, I'm not fully aware 
//     * of all side-effect by setting this to false.*/
//    protected boolean isMultiSorted() {
//	return false;
//    }
    
    /**<p>This method behave just like its overwritten method except for the handling of 
     * quantifiers. It removes type predicates from quantified formulas. In this way
     * far more formulas can be solved by some of the SMT solvers. KeY's type system may
     * be not respected but this may happen in only rare cases.
     * </p>
     * {@inheritDoc} 
     * */
    public StringBuffer translateTerm (Term term, Vector<QuantifiableVariable> quantifiedVars,
	    Services services) throws IllegalFormulaException {
	
	//added, because meatavariables should not be translated.
	if (term.op() instanceof Metavariable) {
	    throw new IllegalFormulaException("The Formula contains a metavariable:\n" +
	    		term.op().toString() + "\n" +
	    		"Metavariables can not be translated.");
	}
	
	Operator op = term.op();
	 if (op == Op.ALL) {
		    ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
		    Debug.assertTrue(vars.size() == 1);

		    quantifiedVars.add(vars.get(0));

		    StringBuffer qv = this.translateVariable(vars
			    .get(0));
		    StringBuffer sort = this.translateSort(vars
			    .get(0).sort());
		    StringBuffer form = this.translateTerm(term.sub(0), quantifiedVars,
			    services);
//The commented out code is the difference to the original implementation
//		    if (!this.isMultiSorted() || !isSomeIntegerSort(vars.get(0).sort())) {
//			// add the typepredicate
//			// this is not needed, if the variable, that is quantified over is of
//			// some integer type and in Multisort mode
//			form = this.translateLogicalImply(this.getTypePredicate(vars
//				.get(0).sort(), qv), form);
//		    }

		    quantifiedVars.remove(vars.get(0));

		    return this.translateLogicalAll(qv, sort, form);

	} else if (op == Op.EX) {
		    ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
		    Debug.assertTrue(vars.size() == 1);

		    quantifiedVars.add(vars.get(0));

		    StringBuffer qv = this.translateVariable(vars
			    .get(0));
		    StringBuffer sort = this.translateSort(vars
			    .get(0).sort());
		    StringBuffer form = this.translateTerm(term.sub(0), quantifiedVars,
			    services);

//The commented out code is the difference to the original implementation
//		    if (!this.isMultiSorted() || !isSomeIntegerSort(vars.get(0).sort())) {
//			// add the typepredicate
//			// a and is needed!!
//			//This is not the case, if the variable, that is quantified ofer is of some
//			// integer type
//			form = this.translateLogicalAnd(this.getTypePredicate(vars
//				.get(0).sort(), qv), form);
//		    }
		    quantifiedVars.remove(vars.get(0));

		    return this.translateLogicalExist(qv, sort, form);
	}else{
//Fall-back, use the original implementation
		    return super.translateTerm(term, quantifiedVars, services);
	}
    }
}
