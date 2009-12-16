package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.sort.Sort;

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
}
