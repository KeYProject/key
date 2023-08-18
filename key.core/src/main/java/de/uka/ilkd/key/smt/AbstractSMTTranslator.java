/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;


import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.assumptions.DefaultTacletSetTranslation;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.smt.SMTProblem.sequentToTerm;

/**
 * This abstract class provides a stub for translation of KeY-Formulas to other standards. Formulas
 * are translated in a correct, but not always complete representation of the target standard.
 * Non-first-order elements in a formula are translated as uninterpreted predicates.
 *
 * The translation for standards supporting multiple sorts is oriented on the paper "The Boogie 2
 * Type System: Design and Verification Condition Generation" by Leino and Ruemmer.
 *
 * @author Simon Greiner
 *
 */
public abstract class AbstractSMTTranslator implements SMTTranslator {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractSMTTranslator.class);

    private int nameCounter = 0;

    /** The string used as standard sort for translations */
    private final StringBuilder standardSort = new StringBuilder("u");

    /** The translation result is stored in this variable. */
    protected String text;

    /** remember all function declarations */
    protected static class FunctionWrapper {
        private final StringBuilder name;
        private final Function function;
        private boolean usedForUnique;

        /**
         * @param name
         * @param function
         */
        public FunctionWrapper(StringBuilder name, Function function) {
            super();
            this.name = name;
            this.function = function;
        }

        /**
         * @return the name
         */
        public StringBuilder getName() {
            return name;
        }

        /**
         * @return the function
         */
        public Function getFunction() {
            return function;
        }

        public boolean isUsedForUnique() {
            return usedForUnique;
        }

        public void setUsedForUnique(boolean b) {
            usedForUnique = b;
        }

    }

    // key is the term to identify the bsum, value is the name used for that function.
    private final HashMap<Term, StringBuilder> usedBsumTerms = new LinkedHashMap<>();

    // key is the term to identify the bprod, value is the name used for that function.
    private final HashMap<Term, StringBuilder> usedBprodTerms = new LinkedHashMap<>();

    // key is the term to identify the function binding vars, value is the name used for the
    // function
    private final HashMap<Term, StringBuilder> uninterpretedBindingFunctionNames =
        new LinkedHashMap<>();

    // key is the term to identify the predicate binding vars, value is the name used for the
    // predicate
    private final HashMap<Term, StringBuilder> uninterpretedBindingPredicateNames =
        new LinkedHashMap<>();

    private final HashMap<Operator, ArrayList<Sort>> functionDecls = new LinkedHashMap<>();

    private final HashSet<Function> specialFunctions = new LinkedHashSet<>();

    private final HashMap<Operator, ArrayList<Sort>> predicateDecls = new LinkedHashMap<>();

    private final HashMap<Operator, StringBuilder> usedVariableNames = new LinkedHashMap<>();

    private final HashMap<Operator, StringBuilder> usedFunctionNames = new LinkedHashMap<>();

    private final Collection<FunctionWrapper> usedFunctions = new LinkedList<>();

    private final HashMap<Operator, StringBuilder> usedPredicateNames = new LinkedHashMap<>();

    protected final HashMap<Sort, StringBuilder> usedDisplaySort = new LinkedHashMap<>();

    protected final HashMap<Sort, StringBuilder> usedRealSort = new LinkedHashMap<>();

    private final HashMap<Sort, StringBuilder> typePredicates = new LinkedHashMap<>();

    // used type predicates for constant values, e.g. 1, 2, ...
    private final HashMap<Term, StringBuilder> constantTypePreds = new LinkedHashMap<>();

    /** map used for storing predicates representing modalities or updates */
    private final HashMap<Term, StringBuilder> modalityPredicates = new LinkedHashMap<>();

    /**
     * If a integer is not supported by a solver because it is too big, the integer is translated
     * into a constant. This constants are stored at this place.
     */
    private final HashMap<Long, StringBuilder> constantsForBigIntegers = new LinkedHashMap<>();
    /**
     * If a integer is not supported by a solver because it is too small, the integer is translated
     * into a constant.
     */
    private final HashMap<Long, StringBuilder> constantsForSmallIntegers = new LinkedHashMap<>();

    // assumptions. they have to be added to the formula!
    private final ArrayList<StringBuilder> assumptions = new ArrayList<>();

    /** Formulae made of taclets, used for assumptions. */
    private TacletSetTranslation tacletSetTranslation = null;

    private final Collection<Throwable> exceptionsForTacletTranslation = new LinkedList<>();

    /**
     * Assumptions made of taclets - the translation of <code>tacletFormulae</code>
     */
    private ArrayList<StringBuilder> tacletAssumptions = new ArrayList<>();

    private SMTSettings smtSettings = null;

    /**
     * If the solver supports only simple multiplications, complex multiplications are translated
     * into a uninterpreted function. The name of the function is stored here.
     */
    private Function multiplicationFunction = null;

    private static final String BSUM_STRING = "bsum";

    private static final String BPROD_STRING = "bprod";

    public TacletSetTranslation getTacletSetTranslation() {
        return tacletSetTranslation;
    }

    @Override
    public final StringBuilder translateProblem(Sequent sequent, Services services,
            SMTSettings settings) throws IllegalFormulaException {
        smtSettings = settings;
        Term problem = sequentToTerm(sequent, services);
        StringBuilder hb = translateTerm(problem, new ArrayList<>(), services);

        // add one variable for each sort
        for (Sort s : this.usedRealSort.keySet()) {
            if (!s.equals(Sort.FORMULA)) {
                LogicVariable l = new LogicVariable(new Name("dummy_" + s.name().toString()), s);
                this.addFunction(l, new ArrayList<>(), s, services);
                this.translateFunc(l, new ArrayList<>());
            }
        }

        tacletAssumptions = translateTaclets(services, settings);

        return buildComplText(services, hb, settings);
    }

    public Collection<Throwable> getExceptionsOfTacletTranslation() {
        return exceptionsForTacletTranslation;
    }

    protected final SMTSettings getSettings() {
        return smtSettings;
    }

    private Function getMultiplicationFunction(Services services) {
        if (multiplicationFunction == null) {
            Function reference = services.getTypeConverter().getIntegerLDT().getMul();

            TermBuilder tb = services.getTermBuilder();
            multiplicationFunction = new Function(new Name(tb.newName("unin_mult")),
                reference.sort(), reference.argSorts());
        }
        return multiplicationFunction;
    }

    private boolean isUsingUninterpretedMultiplication() {
        return multiplicationFunction != null;
    }

    /**
     * get the assumptions made by the logic.
     *
     * @param services the services object to be used.
     * @param assumptionTypes
     * @return ArrayList of Formulas, that are assumed to be true.
     */
    private ArrayList<StringBuilder> getAssumptions(Services services,
            ArrayList<ContextualBlock> assumptionTypes, SMTSettings settings)
            throws IllegalFormulaException {
        ArrayList<StringBuilder> toReturn = new ArrayList<>();

        // add the type definitions
        // this means all predicates that are needed for functions to
        // define
        // their result type, all predicates for constants (like number
        // symbols)

        int start = toReturn.size();
        toReturn.addAll(getTypeDefinitions(services));
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION));

        // add the type hierarchy
        // this means, add the typepredicates, that are needed to define
        // for every type, what type they are (direct) subtype of
        start = toReturn.size();
        toReturn.addAll(this.getSortHierarchyPredicates(services, settings));
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_TYPE_HIERARCHY));
        // add the formulas, that make sure, type correctness is kept,
        // also
        // for interpreted functions
        // leave this away. This is not needed, if interpreted int
        // functions are typed by the second type u
        start = toReturn.size();
        if (!this.isMultiSorted()) {
            toReturn.addAll(this.getSpecialSortPredicates(services));
        }
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_SORT_PREDICATES));

        // add the assumptions created during translation
        // for example while translating term if then else
        start = toReturn.size();
        toReturn.addAll(this.assumptions);
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION));

        // add the assumptions that that are made of taclets
        start = toReturn.size();
        toReturn.addAll(this.tacletAssumptions);
        // for(int i=0; i < tacletAssumptions.size(); i++){
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_TACLET_TRANSLATION));
        // }

        start = toReturn.size();
        toReturn.addAll(buildUniqueAssumptions(services));
        assumptionTypes.add(
            new ContextualBlock(start, toReturn.size() - 1, ContextualBlock.ASSUMPTION_DISTINCT));

        start = toReturn.size();
        toReturn.addAll(buildAssumptionsForIntegers());
        assumptionTypes.add(
            new ContextualBlock(start, toReturn.size() - 1, ContextualBlock.ASSUMPTION_INTEGER));
        start = toReturn.size();
        toReturn.addAll(buildAssumptionsForSorts(services));
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_SORTS_NOT_EMPTY));
        start = toReturn.size();
        if (isUsingUninterpretedMultiplication()) {
            toReturn.addAll(buildAssumptionsForUninterpretedMultiplication(services));
        }
        assumptionTypes.add(new ContextualBlock(start, toReturn.size() - 1,
            ContextualBlock.ASSUMPTION_MULTIPLICATION));

        return toReturn;
    }

    /**
     * build the formulas, that make sure, special functions keep typing
     *
     * @return ArrayList of formulas, assuring the assumption.
     */
    private ArrayList<StringBuilder> getSpecialSortPredicates(Services services)
            throws IllegalFormulaException {
        ArrayList<StringBuilder> toReturn = new ArrayList<>();

        for (Function o : this.specialFunctions) {

            ArrayList<StringBuilder> varList = new ArrayList<>();
            ArrayList<StringBuilder> predList = new ArrayList<>();
            // build the variables and typepredicates for
            // quantification
            for (int i = 0; i < o.arity(); i++) {
                StringBuilder var = this.translateLogicalVar(new StringBuilder("tvar" + i));
                varList.add(var);
                ArrayList<StringBuilder> templist = new ArrayList<>();
                templist.add(var);
                StringBuilder temppred = this.typePredicates.get(o.argSort(i));
                predList.add(this.translatePredicate(temppred, templist));
            }

            // build the left side of the implication
            StringBuilder leftForm = predList.get(0);
            for (int i = 1; i < predList.size(); i++) {
                leftForm = this.translateLogicalAnd(leftForm, predList.get(i));
            }

            // build the right side of the implication
            StringBuilder rightForm = new StringBuilder();

            // use the interpreted function here!!
            if (o == services.getTypeConverter().getIntegerLDT().getAdd()) {
                rightForm = this.translateIntegerPlus(varList.get(0), varList.get(1));
            } else if (o == services.getTypeConverter().getIntegerLDT().getSub()) {
                rightForm = this.translateIntegerMinus(varList.get(0), varList.get(1));
            } else if (o == services.getTypeConverter().getIntegerLDT().getMul()) {
                rightForm = this.translateIntegerMult(varList.get(0), varList.get(1));
            } else if (o == services.getTypeConverter().getIntegerLDT().getDiv()) {
                rightForm = this.translateIntegerDiv(varList.get(0), varList.get(1));
            }

            StringBuilder rightPred = this.typePredicates.get(o.sort());
            ArrayList<StringBuilder> tempList = new ArrayList<>();
            tempList.add(rightForm);
            rightForm = this.translatePredicate(rightPred, tempList);

            StringBuilder form = this.translateLogicalImply(leftForm, rightForm);

            for (StringBuilder stringBuilder : varList) {
                form = this.translateLogicalAll(stringBuilder, this.getIntegerSort(), form);
            }

            toReturn.add(form);
        }

        return toReturn;
    }

    private StringBuilder buildComplText(Services serv, StringBuilder formula, SMTSettings settings)
            throws IllegalFormulaException {
        ArrayList<ContextualBlock> assumptionTypes = new ArrayList<>();
        ArrayList<ContextualBlock> predicateTypes = new ArrayList<>();
        return buildCompleteText(formula, this.getAssumptions(serv, assumptionTypes, settings),
            assumptionTypes, this.buildTranslatedFuncDecls(serv),
            this.buildTranslatedPredDecls(predicateTypes), predicateTypes,
            this.buildTranslatedSorts(), this.buildSortHierarchy(serv, settings), settings);
    }

    /**
     * Build the sorthierarchy for the sorts If null was used, add typepredicates for all types.
     *
     * @return a sort hierarchy for the sorts
     */
    private SortHierarchy buildSortHierarchy(Services services, SMTSettings settings) {

        return new SortHierarchy(this.usedDisplaySort, this.typePredicates,
            settings.instantiateNullAssumption(), settings.useExplicitTypeHierarchy(), services);

    }

    /**
     * Get the expression for that defines the typepredicates for sort hierarchy. Also the null type
     * is added to the formula if used before.
     *
     * @return The well defined formula.
     */
    private ArrayList<StringBuilder> getSortHierarchyPredicates(Services services,
            SMTSettings settings) {
        Function nullOp = services.getTypeConverter().getHeapLDT().getNull();
        SortHierarchy sh = this.buildSortHierarchy(services, settings);
        ArrayList<StringBuilder> toReturn = new ArrayList<>();
        List<SortWrapper> list = sh.getSorts();
        for (SortWrapper swChild : list) {
            for (SortWrapper swParent : swChild.getParents()) {
                StringBuilder form;
                if (swChild.getSort() == nullOp.sort() && settings.instantiateNullAssumption()) {
                    form = buildInstantiatedHierarchyPredicate(swChild, swParent, translateNull());
                } else {
                    form = buildGeneralHierarchyPredicate(swChild, swParent);
                }

                if (form.length() > 0) {
                    toReturn.add(form);
                }
            }
        }

        return toReturn;
    }

    private StringBuilder buildGeneralHierarchyPredicate(SortWrapper child, SortWrapper parent) {

        StringBuilder var = this.translateLogicalVar(new StringBuilder("tvar2"));
        ArrayList<StringBuilder> varlist = new ArrayList<>();
        varlist.add(var);
        StringBuilder leftForm = this.translatePredicate(child.getPredicateName(), varlist);
        StringBuilder rightForm = this.translatePredicate(parent.getPredicateName(), varlist);

        StringBuilder form = this.translateLogicalImply(leftForm, rightForm);
        if (this.isMultiSorted()) {
            form = this.translateLogicalAll(var, this.standardSort, form);
        } else {
            form = this.translateLogicalAll(var, this.getIntegerSort(), form);
        }
        return form;
    }

    private StringBuilder buildInstantiatedHierarchyPredicate(SortWrapper child, SortWrapper parent,
            StringBuilder constant) {
        ArrayList<StringBuilder> varlist = new ArrayList<>();
        varlist.add(constant);

        return this.translatePredicate(parent.getPredicateName(), varlist);
    }

    /**
     * Returns a set of formula s, that defines the resulttypes of functions, all constants and
     * other elements (i.e. constant number symbols).
     *
     * @return see above
     */
    private ArrayList<StringBuilder> getTypeDefinitions(Services services) {
        ArrayList<StringBuilder> toReturn = new ArrayList<>();

        // add the type definitions for functions
        for (Operator op : functionDecls.keySet()) {
            StringBuilder currentForm = this.getSingleFunctionDef(this.usedFunctionNames.get(op),
                functionDecls.get(op), services);
            if (currentForm.length() > 0) {
                // Do not add it, if an empty result was
                // returned.
                // might lead to confusions.
                toReturn.add(currentForm);
            }
        }

        // add the type predicates for constant values like number
        // symbols
        if (!this.isMultiSorted()) {
            toReturn.addAll(this.constantTypePreds.values());
        }

        return toReturn;
    }

    /**
     * Get the type predicate definition for a given function. If the result type is of some int
     * type, empty StringBuilder is returned.
     *
     * @param funName the name of the function.
     * @param sorts the sorts, the function is defined for. Last element is the return type.
     * @return well formed expression that defines the type of the function.
     */
    private StringBuilder getSingleFunctionDef(StringBuilder funName, ArrayList<Sort> sorts,
            Services services) {
        StringBuilder toReturn = new StringBuilder();

        /*
         * given: the name of a function and its sorts.
         *
         * in case of MultiSort-mode: if the functions result is of some non-integer type returned:
         * for all tvar1:displaysort1,...,tvarn:displaysortn : [type_of_sort1(tvar1) AND ...
         * type_of_sortn(tvarn)] implies type_of_n+1(funcName(tvar1, ..., tvarn))
         *
         * if one of the arguments are of sort int, skip their type atrribute. if all of them are,
         * skip lefthandside of the implication
         */
        int firstIndex = -1;
        if (!this.isMultiSorted() || !isSomeIntegerSort(sorts.get(sorts.size() - 1), services)) {
            // collect the quantify vars
            ArrayList<StringBuilder> qVar = new ArrayList<>();
            for (int i = 0; i < sorts.size() - 1; i++) {
                qVar.add(this.translateLogicalVar(new StringBuilder("tvar")));
            }

            // left hand side of the type implication
            if (!this.isMultiSorted()) {
                if (qVar.size() > 0) {
                    toReturn = this.getTypePredicate(sorts.get(0), qVar.get(0));
                }
                for (int i = 1; i < qVar.size(); i++) {
                    StringBuilder temp = getTypePredicate(sorts.get(i), qVar.get(i));
                    toReturn = this.translateLogicalAnd(toReturn, temp);
                }
            } else {
                // find the first non-int sort

                for (int i = 0; i < qVar.size() && firstIndex == -1; i++) {
                    if (!isSomeIntegerSort(sorts.get(i), services)) {
                        firstIndex = i;
                        toReturn = this.getTypePredicate(sorts.get(i), qVar.get(i));
                    }
                }

                for (int i = firstIndex + 1; i < qVar.size() && firstIndex > -1; i++) {
                    if (!isSomeIntegerSort(sorts.get(i), services)) {
                        StringBuilder temp = getTypePredicate(sorts.get(i), qVar.get(i));
                        toReturn = this.translateLogicalAnd(toReturn, temp);
                    }
                }
            }
            // build the right side
            StringBuilder rightSide;
            rightSide = this.translateFunction(funName, qVar);
            rightSide = getTypePredicate(sorts.get(sorts.size() - 1), rightSide);

            if (!this.isMultiSorted()) {
                if (qVar.size() > 0) {
                    toReturn = this.translateLogicalImply(toReturn, rightSide);
                } else {
                    toReturn = rightSide;
                }
            } else {
                if (firstIndex > -1) {
                    toReturn = this.translateLogicalImply(toReturn, rightSide);
                } else {
                    toReturn = rightSide;
                }
            }

            // built the forall around it
            for (int i = qVar.size() - 1; i >= 0; i--) {
                toReturn = this.translateLogicalAll(qVar.get(i),
                    this.usedDisplaySort.get(sorts.get(i)), toReturn);
            }

            return toReturn;
        } else {
            /*
             * the function is of some int type. Welldefinedness is not needed to be axiomated. The
             * returntype is defined via the int type, the welldefinedness of the arguments is
             * defined by construction (also used above).
             */
            return toReturn;
        }

    }

    /**
     * Build the translated function declarations. Each element in the ArrayList represents
     * (functionname | argType1 | ... | argTypen| resultType)
     *
     * @return structured List of declaration.
     */
    private ArrayList<ArrayList<StringBuilder>> buildTranslatedFuncDecls(Services services) {
        ArrayList<ArrayList<StringBuilder>> toReturn = new ArrayList<>();
        // add the function declarations for each used function
        for (Operator op : this.functionDecls.keySet()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(usedFunctionNames.get(op));
            for (Sort s : functionDecls.get(op)) {
                if (s == Sort.FORMULA) {
                    // This function was used with a formula as argument. Treat like a boolean sort
                    element.add(this.getBoolSort());
                } else {
                    element.add(usedDisplaySort.get(s));
                }
            }
            toReturn.add(element);
        }

        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();

        // add the type definitions for the bsum function symbols
        for (StringBuilder sb : usedBsumTerms.values()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(sb);
            element.add(usedDisplaySort.get(integerSort));
            element.add(usedDisplaySort.get(integerSort));
            element.add(usedDisplaySort.get(integerSort));
            toReturn.add(element);
        }

        // add the type definitions for the bprod function symbols
        for (StringBuilder sb : usedBprodTerms.values()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(sb);
            element.add(usedDisplaySort.get(integerSort));
            element.add(usedDisplaySort.get(integerSort));
            element.add(usedDisplaySort.get(integerSort));
            toReturn.add(element);
        }

        // add the type definition for uninterpreted binding functions
        for (Term t : uninterpretedBindingFunctionNames.keySet()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(uninterpretedBindingFunctionNames.get(t));
            Function f = (Function) t.op();
            for (int i = 0; i < f.arity(); i++) {
                if (!f.bindVarsAt(i)) {
                    element.add(usedDisplaySort.get(f.argSort(i)));
                }
            }
            // add the sort definitions for the free variables of the bound terms
            for (int j = 0; j < f.arity(); j++) {
                if (f.bindVarsAt(j)) {
                    Iterator<QuantifiableVariable> iter = t.sub(j).freeVars().iterator();
                    ImmutableArray<QuantifiableVariable> bv = t.boundVars();
                    while (iter.hasNext()) {
                        QuantifiableVariable q = iter.next();
                        boolean isBound = false;
                        for (QuantifiableVariable temp : bv) {
                            isBound = isBound || temp.equals(q);
                        }
                        if (!isBound) {
                            // add on position 1, since position 0 is used for the function name
                            element.add(1, usedDisplaySort.get(q.sort()));
                        }
                    }
                }
            }

            element.add(usedDisplaySort.get(f.sort()));
            toReturn.add(element);
        }

        /*
         * if (this.nullUsed) { //add the null constant to the declarations ArrayList<StringBuilder>
         * a = new ArrayList<StringBuilder>(); a.add(this.nullString); if (this.isMultiSorted()) {
         * a.add(this.standardSort); } else { a.add(this.getIntegerSort()); } toReturn.add(a); }
         */

        // add the definition of the cast function
        if (this.isMultiSorted() && this.castPredicate != null) {
            // it was used at least once
            ArrayList<StringBuilder> temp = new ArrayList<>();
            temp.add(this.castPredicate);
            temp.add(this.getIntegerSort());
            temp.add(this.standardSort);
            toReturn.add(temp);
        }

        return toReturn;
    }

    /**
     * Build the translated predicate declarations. Each element in the ArrayList represents
     * (predicatename | argType1 | ... | argTypen)
     *
     * @return structured List of declaration.
     */
    private ArrayList<ArrayList<StringBuilder>> buildTranslatedPredDecls(
            ArrayList<ContextualBlock> predicateTypes) {
        ArrayList<ArrayList<StringBuilder>> toReturn = new ArrayList<>();

        int start = toReturn.size();
        // add the predicates

        for (Operator op : this.predicateDecls.keySet()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(usedPredicateNames.get(op));
            for (Sort s : predicateDecls.get(op)) {
                element.add(usedDisplaySort.get(s));
            }
            toReturn.add(element);
        }

        // add the uninterpreted predicates binding vars
        for (Term t : this.uninterpretedBindingPredicateNames.keySet()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(uninterpretedBindingPredicateNames.get(t));
            for (int i = 0; i < t.op().arity(); i++) {
                if (!t.op().bindVarsAt(i)) {
                    element.add(usedDisplaySort.get(t.sub(i).sort()));
                }
            }

            // add the sort definitions for the free variables of the bound terms
            for (int j = 0; j < t.op().arity(); j++) {
                if (t.op().bindVarsAt(j)) {
                    Iterator<QuantifiableVariable> iter = t.sub(j).freeVars().iterator();
                    ImmutableArray<QuantifiableVariable> bv = t.boundVars();
                    while (iter.hasNext()) {
                        QuantifiableVariable q = iter.next();
                        boolean isBound = false;
                        for (QuantifiableVariable temp : bv) {
                            isBound = isBound || (temp.equals(q));
                        }
                        if (!isBound) {
                            // add on position 1, because position 0 is ised for the predicate name
                            element.add(1, usedDisplaySort.get(q.sort()));
                        }
                    }
                }
            }


            toReturn.add(element);
        }

        predicateTypes.add(
            new ContextualBlock(start, toReturn.size() - 1, ContextualBlock.PREDICATE_FORMULA));

        // add the typePredicates

        start = toReturn.size();

        for (Sort s : this.typePredicates.keySet()) {
            ArrayList<StringBuilder> element = new ArrayList<>();
            element.add(typePredicates.get(s));
            if (!this.isMultiSorted()) {
                element.add(this.usedDisplaySort.get(s));
            } else {
                // type predicates can only be used for
                // standardSort, never for integer sorts.
                // always tape cast needed for this.
                element.add(this.standardSort);
            }
            toReturn.add(element);
        }

        predicateTypes.add(
            new ContextualBlock(start, toReturn.size() - 1, ContextualBlock.PREDICATE_TYPE));
        return toReturn;
    }

    /**
     * ArrayList of all sorts, that were used as sorts. Including the integer sort.
     *
     * @return ArrayList of the names of sorts.
     */
    private ArrayList<StringBuilder> buildTranslatedSorts() {
        ArrayList<StringBuilder> toReturn = new ArrayList<>();

        if (!this.isMultiSorted()) {
            for (Sort s : this.usedDisplaySort.keySet()) {
                StringBuilder newSort = this.usedDisplaySort.get(s);
                // make sure, no sort is added twice!!
                boolean alreadyIn = false;
                for (StringBuilder stringBuilder : toReturn) {
                    if (stringBuilder.equals(newSort)) {
                        alreadyIn = true;
                        break;
                    }
                }
                if (!alreadyIn) {
                    toReturn.add(newSort);
                }
            }
        } else {
            // add the two sorts needed as maximum
            toReturn.add(this.standardSort);
            toReturn.add(this.getIntegerSort());
        }
        return toReturn;
    }

    private ArrayList<StringBuilder> buildUniqueAssumptions(Services services)
            throws IllegalFormulaException {

        ArrayList<StringBuilder> distinct = new ArrayList<>();

        for (FunctionWrapper function : usedFunctions) {
            if (function.getFunction().isUnique()) {
                StringBuilder buffer = translateUniqueness(function, usedFunctions, services);
                if (buffer != null) {
                    distinct.add(buffer);
                }

            }
        }
        return distinct;
    }



    private Term createLogicalVar(Services services, String baseName, Sort sort) {
        TermBuilder tb = services.getTermBuilder();
        return tb.var(new LogicVariable(new Name(tb.newName(baseName)), sort));
    }

    private ArrayList<StringBuilder> buildAssumptionsForUninterpretedMultiplication(
            Services services) throws IllegalFormulaException {
        ArrayList<StringBuilder> result = new ArrayList<>();
        Sort sort = services.getTypeConverter().getIntegerLDT().getMul().sort();
        Function mult = getMultiplicationFunction(services);
        TermBuilder tb = services.getTermBuilder();
        Term zero = tb.zero();
        Term one = tb.one();
        LinkedList<Term> multAssumptions = new LinkedList<>();

        Term x = createLogicalVar(services, "x", sort);
        Term y = createLogicalVar(services, "y", sort);
        Term z = createLogicalVar(services, "z", sort);
        multAssumptions.add(tb.equals(tb.func(mult, x, zero), zero));
        multAssumptions.add(tb.equals(tb.func(mult, zero, x), zero));
        multAssumptions.add(tb.equals(tb.func(mult, x, one), x));
        multAssumptions.add(tb.equals(tb.func(mult, one, x), x));
        multAssumptions.add(tb.equals(tb.func(mult, x, y), tb.func(mult, y, x)));
        multAssumptions.add(tb.equals(tb.func(mult, tb.func(mult, y, x), z),
            tb.func(mult, y, tb.func(mult, x, z))));
        multAssumptions.add(tb.imp(tb.equals(tb.func(mult, x, y), zero),
            tb.or(tb.equals(x, zero), tb.equals(y, zero))));
        multAssumptions.add(tb.imp(tb.equals(tb.func(mult, x, y), one),
            tb.and(tb.equals(x, one), tb.equals(y, one))));
        for (Term assumption : multAssumptions) {
            assumption = tb.allClose(assumption);
            result.add(translateTerm(assumption, new ArrayList<>(), services));
        }
        return result;
    }

    private ArrayList<StringBuilder> buildAssumptionsForIntegers() throws IllegalFormulaException {
        ArrayList<StringBuilder> result = new ArrayList<>();
        result.addAll(buildAssumptionsForIntegers(this.constantsForBigIntegers.values(), true));
        result.addAll(buildAssumptionsForIntegers(this.constantsForSmallIntegers.values(), false));
        return result;
    }

    private ArrayList<StringBuilder> buildAssumptionsForIntegers(
            Collection<StringBuilder> constants, boolean upperBound)
            throws IllegalFormulaException {
        ArrayList<StringBuilder> result = new ArrayList<>();
        for (StringBuilder constant : constants) {
            if (upperBound) {
                result.add(translateIntegerLt(translateIntegerValue(getMaxNumber()), constant));
            } else {
                result.add(translateIntegerGt(translateIntegerValue(getMinNumber()), constant));
            }
        }
        return result;
    }

    private ArrayList<StringBuilder> buildAssumptionsForSorts(Services services) {
        ArrayList<StringBuilder> result = new ArrayList<>();
        if (this.isMultiSorted()) {
            for (Sort sort : usedRealSort.keySet()) {

                // Do not add Assumptions for Boolean or integer sorts
                if (!isSomeIntegerSort(sort, services) && sort != Sort.FORMULA) {
                    Term var = createLogicalVar(services, "x", sort);
                    StringBuilder sVar = translateVariable(var.op());
                    // StringBuilder var = this.makeUnique(new StringBuilder("x"));
                    StringBuilder typePredicate = this.getTypePredicate(sort, sVar);
                    StringBuilder assumption =
                        translateLogicalExist(sVar, this.standardSort, typePredicate);
                    result.add(assumption);
                }
            }
        }
        return result;
    }

    private HashMap<Long, StringBuilder> getRightConstantContainer(long integer) {
        return integer < 0 ? constantsForSmallIntegers : constantsForBigIntegers;
    }

    private Term getRightBorderAsTerm(long integer, Services services) {
        TermBuilder tb = services.getTermBuilder();
        return tb.zTerm(Long.toString(getRightBorderAsInteger(integer, services)));
    }

    private Long getRightBorderAsInteger(long integer, TermServices services) {
        return integer < 0 ? getMinNumber() : getMaxNumber();
    }

    private StringBuilder getNameForIntegerConstant(Services services, long integer) {
        String val = integer < 0 ? "negative_value" : "positive_value";
        TermBuilder tb = services.getTermBuilder();
        return new StringBuilder(tb.newName("i") + "_" + val);

    }

    private StringBuilder buildUniqueConstant(long integer, Services services)
            throws IllegalFormulaException {
        HashMap<Long, StringBuilder> map = getRightConstantContainer(integer);
        StringBuilder buf = map.get(integer);
        if (buf != null) {
            return buf;
        }
        StringBuilder name = translateFunctionName(getNameForIntegerConstant(services, integer));
        buf = translateFunction(name, new ArrayList<>());
        map.put(integer, buf);
        Term term = getRightBorderAsTerm(integer, services);
        addConstantTypePredicate(term,
            translateIntegerValue(getRightBorderAsInteger(integer, services)), services);
        return buf;
    }

    /**
     * Build the text, that can be read by the final decider. If the assumptions should be added to
     * the formula, add them like assumtions impliy formula.
     *
     * @param formula The formula, that was built out of the internal representation. It is built by
     *        ante implies succ.
     * @param assum Assumptions made in this logic. Set of formulas, that are assumed to be true.
     * @param assumptionBlocks List of ContextualBlocks, which refer to the position of different
     *        types of assumptions in the container <code>assumptions</code>. Use these objects to
     *        make detailed comments in the translations. For more information see the class
     *        <code>ContextualBlock</code> .
     * @param functions List of functions. Each Listelement is built up like (name | sort1 | ... |
     *        sortn | resultsort)
     * @param predicates List of predicates. Each Listelement is built up like (name | sort1 | ... |
     *        sortn)
     * @param predicateBlocks List of ContextualBlocks, which refer to the position of different
     *        types of predicate in the container <code>predicates</code>. Use these objects to make
     *        detailed comments in the translations. For more information see the class
     *        <code>ContextualBlock</code> .
     * @param types List of the used types.
     * @return The StringBuilder that can be read by the decider
     */
    protected abstract StringBuilder buildCompleteText(StringBuilder formula,
            ArrayList<StringBuilder> assum, ArrayList<ContextualBlock> assumptionBlocks,
            ArrayList<ArrayList<StringBuilder>> functions,
            ArrayList<ArrayList<StringBuilder>> predicates,
            ArrayList<ContextualBlock> predicateBlocks, ArrayList<StringBuilder> types,
            SortHierarchy sortHierarchy, SMTSettings settings);

    /**
     * Returns, whether the Structure, this translator creates should be a Structure, that is multi
     * sorted. If false, a single sorted structure is created. Then all sorts are translated as
     * integers.
     *
     * @return true, if multi sorted logic is supported.
     */
    protected abstract boolean isMultiSorted();

    /**
     * The String used for integer values. This sort is also used in single sorted logics.
     *
     * @return The String used for integers.
     */
    protected abstract StringBuilder getIntegerSort();

    /**
     * The String used for boolean values.
     *
     * @return The string used for boolean values.
     */
    protected abstract StringBuilder getBoolSort();

    /**
     * Build the StringBuilder for a logical NOT.
     *
     * @param arg The Formula to be negated.
     * @return The StringBuilder representing the resulting Formular
     */
    protected abstract StringBuilder translateLogicalNot(StringBuilder arg);

    /**
     * Build the logical konjunction.
     *
     * @param arg1 The first formula.
     * @param arg2 The second formula.
     * @return The StringBuilder representing the resulting formular.
     */
    protected abstract StringBuilder translateLogicalAnd(StringBuilder arg1, StringBuilder arg2);

    /**
     * Build the logical disjunction.
     *
     * @param arg1 The first formula.
     * @param arg2 The second formula.
     * @return The StringBuilder representing the resulting formular.
     */
    protected abstract StringBuilder translateLogicalOr(StringBuilder arg1, StringBuilder arg2);

    /**
     * Build the logical implication.
     *
     * @param arg1 The first formula.
     * @param arg2 The second formula.
     * @return The StringBuilder representing the resulting formular
     */
    protected abstract StringBuilder translateLogicalImply(StringBuilder arg1, StringBuilder arg2);

    /**
     * Build the logical equivalence.
     *
     * @param arg1 The first formula.
     * @param arg2 The second formula.
     * @return The StringBuilder representing the resulting formular
     */
    protected abstract StringBuilder translateLogicalEquivalence(StringBuilder arg1,
            StringBuilder arg2);

    /**
     * Build the logical forall formula.
     *
     * @param var the bounded variable.
     * @param type the type of the bounded variable.
     * @param form The formula containing the bounded variable.
     * @return The resulting formula.
     */
    protected abstract StringBuilder translateLogicalAll(StringBuilder var, StringBuilder type,
            StringBuilder form);

    /**
     * Build the logical exists formula.
     *
     * @param var the bounded variable.
     * @param type the type of the bounded variable.
     * @param form The formula containing the bounded variable.
     * @return The resulting formula.
     */
    protected abstract StringBuilder translateLogicalExist(StringBuilder var, StringBuilder type,
            StringBuilder form);

    /**
     * Translate the logical true.
     *
     * @return The StringBuilder the logical true value.
     */
    protected abstract StringBuilder translateLogicalTrue();

    /**
     * Translate the logical false.
     *
     * @return The StringBuilder the logical false value.
     */
    protected abstract StringBuilder translateLogicalFalse();

    /**
     * Build the StringBuilder for an object equivalence.
     *
     * @param arg1 The first formula of the equivalence.
     * @param arg2 The second formula of the equivalence.
     * @return The StringBuilder representing teh resulting Formular
     */
    protected abstract StringBuilder translateObjectEqual(StringBuilder arg1, StringBuilder arg2);

    /**
     * Build the StringBuilder for an variable.
     *
     * @return The StringBuilder representing the resulting Formular
     */
    protected abstract StringBuilder translateLogicalVar(StringBuilder name);

    /**
     * Build the StringBuilder for an constant.
     *
     * @return The StringBuilder representing the resulting Formular
     */
    protected abstract StringBuilder translateLogicalConstant(StringBuilder name);

    /**
     * Translate a predicate.
     *
     * @param name The Symbol of the predicate.
     * @param args The arguments of the predicate.
     * @return the formula representing the predicate.
     */
    protected abstract StringBuilder translatePredicate(StringBuilder name,
            ArrayList<StringBuilder> args);

    /**
     * Get the name for a predicate symbol.
     *
     * @param name The name that can be used to create the symbol.
     * @return The unique predicate symbol.
     */
    protected abstract StringBuilder translatePredicateName(StringBuilder name);

    /**
     * Translate a function.
     *
     * @param name The Symbol of the function.
     * @param args The arguments of the function.
     * @return the formula representing the function.
     */
    protected abstract StringBuilder translateFunction(StringBuilder name,
            ArrayList<StringBuilder> args);

    /**
     * Get the name for a function symbol.
     *
     * @param name The name that can be used to create the symbol.
     * @return The unique function symbol.
     */
    protected abstract StringBuilder translateFunctionName(StringBuilder name);

    /**
     * Translate the integer plus.
     *
     * @param arg1 first val of the sum.
     * @param arg2 second val of the sum.
     * @return The formula representing the integer plus.
     */
    protected StringBuilder translateIntegerPlus(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException("Integer addition is not supported by this translator.");

    }

    /**
     * Translate the integer minus.
     *
     * @param arg1 The first val of the substraction.
     * @param arg2 second val of the substraction.
     * @return The formula representing the integer substraction.
     */
    protected StringBuilder translateIntegerMinus(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException(
            "Integer subtraction is not supported by this translator.");

    }

    /**
     * Translate a unary minus.
     *
     * @param arg the argument of the unary minus.
     * @return the formula representing tha unary minus function.
     */
    protected StringBuilder translateIntegerUnaryMinus(StringBuilder arg)
            throws IllegalFormulaException {

        throw new IllegalFormulaException("negative numbers are not supported by this translator.");

    }

    /**
     * Translate the integer multiplication.
     *
     * @param arg1 The first val of the multiplication.
     * @param arg2 second val of the multiplication.
     * @return The formula representing the integer multiplication.
     */
    protected StringBuilder translateIntegerMult(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException(
            "Integer multiplication is not supported by this translator.");

    }

    /**
     * Translate the integer division. Override this, if integer division is supported.
     *
     * @param arg1 The first val of the division.
     * @param arg2 second val of the division.
     * @return The formula representing the integer division.
     */
    protected StringBuilder translateIntegerDiv(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException("Integer division is not supported by this translator.");

    }

    /**
     * Translate the integer modulo. Override this, if integer modulo is supported.
     *
     * @param arg1 The first val of the modulo.
     * @param arg2 second val of the modulo.
     * @return The formula representing the integer modulo.
     */
    protected StringBuilder translateIntegerMod(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException("Integer modulo is not supported by this translator.");

    }

    /**
     * Translate the greater than. Override this, if integer greater is supported.
     *
     * @param arg1 The first val of the greater than.
     * @param arg2 second val of the greater than.
     * @return The formula representing the greater than.
     */
    protected StringBuilder translateIntegerGt(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException("Integer greater is not supported by this translator.");

    }

    /**
     * Translate the less than. Override this, if integer less is supported.
     *
     * @param arg1 The first val of the less than.
     * @param arg2 second val of the less than.
     * @return The formula representing the less than.
     */
    protected StringBuilder translateIntegerLt(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException("Integer less is not supported by this translator.");

    }

    /**
     * Translate the greater or equal. Override this, if integer greater or equal is supported.
     *
     * @param arg1 The first val of the greater or equal.
     * @param arg2 second val of the greater or equal.
     * @return The formula representing the greater or equal.
     */
    protected StringBuilder translateIntegerGeq(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException(
            "Integer greater or equal is not supported by this translator.");

    }

    /**
     * Translate the less or equal. Override this, if integer less or equal is supported.
     *
     * @param arg1 The first val of the less or equal.
     * @param arg2 second val of the less or equal.
     * @return The formula representing the less or equal.
     */
    protected StringBuilder translateIntegerLeq(StringBuilder arg1, StringBuilder arg2)
            throws IllegalFormulaException {

        throw new IllegalFormulaException(
            "Integer less or equal is not supported by this translator.");

    }


    /**
     * Translate the NULL element
     *
     * @return the StringBuilder used for nullelement
     */
    protected abstract StringBuilder translateNull();

    /**
     *
     * @return Returns the name of the NULL element.
     */
    protected abstract StringBuilder getNullName();

    /**
     * Translate the NULL element's Sort.
     *
     * @return the StringBuilder used for Null.
     */
    protected abstract StringBuilder translateNullSort();

    /**
     * Translate a sort.
     *
     * @param name the sorts name
     * @param isIntVal true, if the sort should represent some kind of integer
     *
     * @return The String used for this sort. If Multisorted, used in declarations, else for the
     *         typepredicates.
     */
    protected abstract StringBuilder translateSort(String name, boolean isIntVal);

    /**
     * Translate a sort. Return the StringBuilder, that should be displayed at definitionpart. i.e.
     * the name used for typepredicates an similair. Override this, if integers are supported.
     *
     * @return the sorts name
     */
    protected StringBuilder translateIntegerValue(long val) throws IllegalFormulaException {

        throw new IllegalFormulaException("Integer numbers are not supported by this translator.");

    }

    /**
     * Translate the logical if_then_else construct. All attributes are logical formulas. If the
     * underlying language does not support this contruct, it is equivalent with (cond IMPLIES
     * ifterm) AND (NOT(cond) IMPLIES thenterm) and can be reduced to this.
     *
     * @param cond the condition term.
     * @param ifterm the formula used, if cond=true
     * @param elseterm the term used, if cond=false
     * @return ther StringBuilder representing the if then else construct
     */
    protected abstract StringBuilder translateLogicalIfThenElse(StringBuilder cond,
            StringBuilder ifterm, StringBuilder elseterm);

    /**
     * Translate the if_then_else construct for terms (i.e. ifterm and condterm are not of Sort
     * FORMULA) If this method is nor overriden, a default implementation is used. This might me
     * less effective than a language supported translation. So, if allowed by the target language,
     * override this.
     *
     * @param cond the condition formula
     * @param ifterm the term used if cond = true.
     * @param elseterm the term used if cond = false.
     * @return the StringBuilder representing the if then else construct.
     * @throws IllegalFormulaException if this construct is not supported.
     */
    protected StringBuilder translateTermIfThenElse(StringBuilder cond, StringBuilder ifterm,
            StringBuilder elseterm) throws IllegalFormulaException {

        throw new IllegalFormulaException("The if then else construct for terms is not supported");

    }

    /**
     * Translates the unique-property of a function.
     *
     * @param function the function itself
     * @param distinct the set of functions, that should be distinct.
     * @return the translation of the unique function
     */
    protected StringBuilder translateUniqueness(FunctionWrapper function,
            Collection<FunctionWrapper> distinct, Services services)
            throws IllegalFormulaException {
        if (!function.getFunction().isUnique()) {
            return null;
        }

        function.setUsedForUnique(true);

        StringBuilder result = translateLogicalTrue();
        for (FunctionWrapper fw : distinct) {
            if (!fw.isUsedForUnique() && fw.getFunction().isUnique()) {
                FunctionWrapper[] array = { function, fw };
                if (function.function.sort().extendsTrans(fw.function.sort())
                        || fw.function.sort().extendsTrans(function.function.sort())
                        || fw.function.sort().equals(function.function.sort())) {
                    result = translateLogicalAnd(result, translateDistinct(array, services));
                }

            }
        }
        return translateLogicalAnd(result, buildInjectiveFunctionAssumption(function, services));
    }

    protected StringBuilder buildInjectiveFunctionAssumption(FunctionWrapper fw,
            Services services) {
        if (fw.getFunction().arity() == 0) {
            return translateLogicalTrue();
        }
        StringBuilder result;
        ArrayList<StringBuilder> vars1 = createGenericVariables(fw.getFunction().arity(), 0);
        ArrayList<StringBuilder> vars2 = createGenericVariables(fw.getFunction().arity(), 0);
        StringBuilder function1 = translateFunction(fw.getName(), vars1);
        StringBuilder function2 = translateFunction(fw.getName(), vars2);
        result = translateLogicalNot(translateObjectEqual(function1, function2));
        StringBuilder leftSide = translateLogicalTrue();
        for (int i = 0; i < vars1.size(); i++) {
            StringBuilder eq = translateObjectEqual(vars1.get(i), vars2.get(i));
            leftSide = translateLogicalAnd(leftSide, eq);
        }

        result = translateLogicalOr(leftSide, result);
        result = translateLogicalAll(vars1, getArgSorts(fw.function), result, services);
        result = translateLogicalAll(vars2, getArgSorts(fw.function), result, services);
        return result;
    }

    private ArrayList<Sort> getArgSorts(Function function) {
        ArrayList<Sort> sorts = new ArrayList<>();
        for (Sort sort : function.argSorts()) {
            sorts.add(sort);
        }
        return sorts;
    }

    private StringBuilder createGenericVariable(int pos) {
        return translateLogicalVar(new StringBuilder("n" + pos));
    }

    protected ArrayList<StringBuilder> createGenericVariables(int count, int start) {
        ArrayList<StringBuilder> list = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            list.add(createGenericVariable(i + start));
        }
        return list;
    }

    protected StringBuilder translateDistinct(FunctionWrapper[] functions, Services services) {
        assert functions.length == 2;
        int start = 0;
        StringBuilder[] functionTranslation = new StringBuilder[functions.length];
        ArrayList<StringBuilder> createdVariables = new ArrayList<>();
        ArrayList<Sort> sorts = new ArrayList<>();

        for (int i = 0; i < functions.length; i++) {
            FunctionWrapper fw = functions[i];
            ArrayList<StringBuilder> vars = createGenericVariables(fw.getFunction().arity(), start);
            sorts.addAll(getArgSorts(fw.getFunction()));

            functionTranslation[i] = translateFunction(fw.getName(), vars);
            createdVariables.addAll(vars);
        }

        StringBuilder result = translateObjectEqual(functionTranslation[0], functionTranslation[1]);
        result = translateLogicalNot(result);

        result = translateLogicalAll(createdVariables, sorts, result, services);

        return result;
    }

    protected StringBuilder translateLogicalAll(ArrayList<StringBuilder> variables,
            ArrayList<Sort> sorts, StringBuilder result, Services services) {
        for (int i = 0; i < variables.size(); i++) {
            result = translateLogicalAll(variables.get(i), sorts.get(i), result, services);
        }
        return result;
    }

    protected StringBuilder translateLogicalAll(StringBuilder var, Sort sort, StringBuilder result,
            Services services) {
        return translateLogicalAll(var, translateSort(sort, services), result);
    }

    private final StringBuilder translateTermIte(Term iteTerm,
            List<QuantifiableVariable> quantifiedVars, Services services)
            throws IllegalFormulaException {

        // make typecasts, if this is neccesary. Subterms might contain
        // integer values,
        // but object values are needed
        StringBuilder cond = translateTerm(iteTerm.sub(0), quantifiedVars, services);
        StringBuilder ifterm = translateTerm(iteTerm.sub(1), quantifiedVars, services);
        if (this.isMultiSorted()) {
            ifterm = this.castIfNeccessary(ifterm, iteTerm.sub(1).sort(), iteTerm.sort(), services);
        }
        StringBuilder elseterm = translateTerm(iteTerm.sub(2), quantifiedVars, services);
        if (this.isMultiSorted()) {
            elseterm =
                this.castIfNeccessary(elseterm, iteTerm.sub(2).sort(), iteTerm.sort(), services);
        }
        // try {
        return this.translateTermIfThenElse(cond, ifterm, elseterm);
        // } catch (IllegalFormulaException e) {
        // // the translation of if then else for terms is not
        // // supported, so use default implementation
        // // invent a new constant
        // LogicVariable c = new LogicVariable(
        // new Name("iteConst"), iteTerm.sort());
        // // translate the constant
        // Term t = TermBuilder.DF.var(c);
        // StringBuilder cstr = this.translateTerm(t,
        // quantifiedVars, services);
        // // build an assumption used to specify how c can be used
        // StringBuilder assump = this.translateObjectEqual(cstr,
        // ifterm);
        // assump = this.translateLogicalImply(cond, assump);
        // StringBuilder temp = this.translateObjectEqual(cstr,
        // elseterm);
        // temp = this.translateLogicalImply(
        // this.translateLogicalNot(cond), temp);
        // assump = this.translateLogicalAnd(assump, temp);
        // this.assumptions.add(assump);
        //
        // return cstr;
        // }
    }

    private void addConstantTypePredicate(Term term, StringBuilder name, Services services) {
        if (!this.constantTypePreds.containsKey(term)) {
            this.translateSort(term.sort(), services);
            StringBuilder typePred = this.getTypePredicate(term.sort(), name);
            this.constantTypePreds.put(term, typePred);
        }
    }

    /**
     *
     * Translates the given term into input syntax and adds the resulting string to the
     * StringBuilder sb.
     *
     * @param term the Term which should be written in Simplify syntax
     * @param quantifiedVars a Vector containing all variables that have been bound in super-terms.
     *        It is only used for the translation of modulo terms, but must be looped through until
     *        we get there.
     */
    protected StringBuilder translateTerm(Term term, List<QuantifiableVariable> quantifiedVars,
            Services services) throws IllegalFormulaException {


        Operator op = term.op();
        if (op == Junctor.NOT) {
            StringBuilder arg = translateTerm(term.sub(0), quantifiedVars, services);
            return this.translateLogicalNot(arg);
        } else if (op == Junctor.AND) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
            return this.translateLogicalAnd(arg1, arg2);
        } else if (op == Junctor.OR) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
            return this.translateLogicalOr(arg1, arg2);
        } else if (op == Junctor.IMP) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
            return this.translateLogicalImply(arg1, arg2);
        } else if (op == Equality.EQV) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
            return this.translateLogicalEquivalence(arg1, arg2);
        } else if (op == Equality.EQUALS) {
            /*
             * Make a cast on the subterms, if one is of int type, the other is not
             */
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
            if (this.isMultiSorted() && isSomeIntegerSort(term.sub(0).sort(), services)
                    && !isSomeIntegerSort(term.sub(1).sort(), services)) {
                arg1 = cast(arg1);
            }
            if (this.isMultiSorted() && !isSomeIntegerSort(term.sub(0).sort(), services)
                    && isSomeIntegerSort(term.sub(1).sort(), services)) {
                arg2 = cast(arg2);
            }
            return this.translateObjectEqual(arg1, arg2);
        } else if (op instanceof Modality) {
            // op is a modality. So translate it as an uninterpreted
            // predicate.
            // equal modalities are translated with the same
            // predicate
            return this.getModalityPredicate(term, quantifiedVars, services);
        } else if (op instanceof UpdateApplication) {
            // op is an update. So translate it as an uninterpreted
            // predicate.
            // equal updates are translated with the same predicate.
            return this.getModalityPredicate(term, quantifiedVars, services);
        } else if (op == IfThenElse.IF_THEN_ELSE) {
            if (term.sub(1).sort() == Sort.FORMULA) {
                // a logical if then else was used
                StringBuilder cond = translateTerm(term.sub(0), quantifiedVars, services);
                StringBuilder ifterm = translateTerm(term.sub(1), quantifiedVars, services);
                StringBuilder elseterm = translateTerm(term.sub(2), quantifiedVars, services);
                return translateLogicalIfThenElse(cond, ifterm, elseterm);
            } else {
                // a term if then else was used
                return this.translateTermIte(term, quantifiedVars, services);
            }
        } else if (op == Quantifier.ALL) {
            ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
            Debug.assertTrue(vars.size() == 1);

            quantifiedVars.add(vars.get(0));

            StringBuilder qv = this.translateVariable(vars.get(0));
            StringBuilder sort = this.translateSort(vars.get(0).sort(), services);
            StringBuilder form = this.translateTerm(term.sub(0), quantifiedVars, services);

            if (!this.isMultiSorted() || !isSomeIntegerSort(vars.get(0).sort(), services)) {
                // add the typepredicate
                // this is not needed, if the variable, that is
                // quantified over is of
                // some integer type and in Multisort mode
                form =
                    this.translateLogicalImply(this.getTypePredicate(vars.get(0).sort(), qv), form);
            }

            quantifiedVars.remove(vars.get(0));

            return this.translateLogicalAll(qv, sort, form);

        } else if (op == Quantifier.EX) {
            ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
            Debug.assertTrue(vars.size() == 1);

            quantifiedVars.add(vars.get(0));

            StringBuilder qv = this.translateVariable(vars.get(0));
            StringBuilder sort = this.translateSort(vars.get(0).sort(), services);
            StringBuilder form = this.translateTerm(term.sub(0), quantifiedVars, services);

            if (!this.isMultiSorted() || !isSomeIntegerSort(vars.get(0).sort(), services)) {
                // add the typepredicate
                // a and is needed!!
                // This is not the case, if the variable, that
                // is quantified ofer is of some
                // integer type
                form =
                    this.translateLogicalAnd(this.getTypePredicate(vars.get(0).sort(), qv), form);
            }
            quantifiedVars.remove(vars.get(0));

            return this.translateLogicalExist(qv, sort, form);
        } else if (op == Junctor.TRUE) {
            return this.translateLogicalTrue();
        } else if (op == Junctor.FALSE) {
            return this.translateLogicalFalse();
        } else if (op == services.getTypeConverter().getHeapLDT().getNull()) {
            Function nullOp = services.getTypeConverter().getHeapLDT().getNull();

            addFunction(nullOp, new ArrayList<>(), nullOp.sort(), services);
            translateSort(nullOp.sort(), services);
            return translateNull();
        } else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
            // translate as variable or constant
            if (quantifiedVars.contains(op)) {
                // This variable is used in the scope of a
                // quantifier
                // so translate it as a variable
                return (translateVariable(op));
            } else {
                // this Variable is a free Variable.
                // translate it as a constant.
                ArrayList<StringBuilder> subterms = new ArrayList<>();
                for (int i = 0; i < op.arity(); i++) {
                    subterms.add(translateTerm(term.sub(i), quantifiedVars, services));
                }

                addFunction(op, new ArrayList<>(), term.sort(), services);

                return translateFunc(op, subterms);
            }
        } else if (op instanceof Function) {
            Function fun = (Function) op;
            if (fun.sort() == Sort.FORMULA) {
                // This Function is a predicate, so translate it
                // as such
                if (fun == services.getTypeConverter().getIntegerLDT().getLessThan()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    return this.translateIntegerLt(arg1, arg2);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getGreaterThan()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    return this.translateIntegerGt(arg1, arg2);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getLessOrEquals()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    return this.translateIntegerLeq(arg1, arg2);
                } else if (fun == services.getTypeConverter().getIntegerLDT()
                        .getGreaterOrEquals()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    return this.translateIntegerGeq(arg1, arg2);
                } else {
                    // op is non rigid, so it can be treated
                    // as uniterpreted predicate
                    // check whether it binds variables
                    boolean bindsVars = false;
                    for (int i = 0; i < op.arity(); i++) {
                        bindsVars = bindsVars || op.bindVarsAt(i);
                    }
                    if (bindsVars) {
                        return translateAsBindingUninterpretedPredicate(term, fun, quantifiedVars,
                            term.subs(), services);
                    } else {
                        ArrayList<StringBuilder> subterms = new ArrayList<>();
                        for (int i = 0; i < op.arity(); i++) {
                            StringBuilder subterm =
                                translateTerm(term.sub(i), quantifiedVars, services);
                            // add the typecast, if needed
                            if (this.isMultiSorted()) {
                                subterm = this.castIfNeccessary(subterm, term.sub(i).sort(),
                                    fun.argSort(i), services);
                            }
                            subterms.add(subterm);
                        }
                        ArrayList<Sort> sorts = new ArrayList<>();
                        for (int i = 0; i < fun.arity(); i++) {
                            sorts.add(fun.argSort(i));
                        }
                        this.addPredicate(fun, sorts, services);

                        return translatePred(op, subterms);
                    }
                }
            } else {
                // this Function is a function, so translate it
                // as such
                if (fun == services.getTypeConverter().getIntegerLDT().getAdd()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    // add the function to the used ones
                    this.addSpecialFunction(fun);
                    // return the final translation
                    return this.translateIntegerPlus(arg1, arg2);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getSub()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    // add the function to the used ones
                    this.addSpecialFunction(fun);
                    // return the final translation
                    return this.translateIntegerMinus(arg1, arg2);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getNeg()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    return this.translateIntegerUnaryMinus(arg1);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getMul()) {

                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    // add the function to the used ones
                    this.addSpecialFunction(fun);
                    // return the final translation

                    /*
                     * TODO WP: not needed anymore with the modern SMT solvers we support -> remove
                     */
                    /*
                     * if (isComplexMultiplication(services, term.sub(0), term.sub(1)) &&
                     * config.supportsOnlySimpleMultiplication) { if
                     * (smtSettings.useUninterpretedMultiplicationIfNecessary()) { Function
                     * unin_mult = getMultiplicationFunction(services); return
                     * this.translateAsUninterpretedFunction( unin_mult, quantifiedVars,
                     * term.subs(), services); } else { String mult = LogicPrinter
                     * .quickPrintTerm(term, services); throw new IllegalFormulaException(
                     * "The multiplication " + mult + " is not" +
                     * " supported by this solver.\nThe problem can be" +
                     * " handled by using uninterpreted functions.\nFor more information see the settings of"
                     * + " the SMT integration: Options/SMT Settings/Translation."); } }
                     */

                    return this.translateIntegerMult(arg1, arg2);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getDiv()) {
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    // add the function to the used ones
                    this.addSpecialFunction(fun);
                    // return the final translation
                    return this.translateIntegerDiv(arg1, arg2);
                } else if (isNumberSymbol(services, fun)) {
                    Debug.assertTrue(term.arity() == 1);
                    long num = NumberTranslation.translate(term.sub(0)).longValue();
                    StringBuilder numVal;

                    /*
                     * TODO WP: not needed anymore with the modern SMT solvers we support -> remove
                     */
                    /*
                     * if (hasNumberLimit() && (num < getMinNumber() || num > getMaxNumber())) { if
                     * (smtSettings.useAssumptionsForBigSmallIntegers()) { numVal =
                     * buildUniqueConstant( num, services); } else { throw new
                     * IllegalNumberException( "The number " + num + " is not supported" +
                     * " by this solver. Either it is too big or too small.\nThe problem can be" +
                     * " handled by using uninterpreted constants. For more information see the settings of"
                     * + " the SMT integration: Options/SMT Settings/Translation."); }
                     */
                    // } else {
                    numVal = translateIntegerValue(num);
                    // }

                    // add the type predicate for this
                    // constant
                    addConstantTypePredicate(term, numVal, services);

                    return numVal;
                } else if (fun == services.getTypeConverter().getIntegerLDT().getBsum()) {
                    // the bsum has to be translated in a special fashion in order to ensure
                    // soundness.
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    ArrayList<StringBuilder> subterms = new ArrayList<>();
                    subterms.add(arg1);
                    subterms.add(arg2);

                    return translateBsumFunction(term, subterms);
                } else if (fun == services.getTypeConverter().getIntegerLDT().getBprod()) {
                    // the bprod has to be translated in a special fashion in order to ensure
                    // soundness.
                    StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVars, services);
                    StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVars, services);
                    ArrayList<StringBuilder> subterms = new ArrayList<>();
                    subterms.add(arg1);
                    subterms.add(arg2);

                    return translateBprodFunction(term, subterms);
                } else {
                    boolean bindsVars = false;
                    for (int i = 0; i < fun.arity(); i++) {
                        bindsVars = bindsVars || fun.bindVarsAt(i);
                    }
                    if (bindsVars) {
                        return translateAsBindingUninterpretedFunction(term, fun, quantifiedVars,
                            term.subs(), services);
                    } else {
                        return translateAsUninterpretedFunction(fun, quantifiedVars, term.subs(),
                            services);
                    }
                }
            }
        } else {
            // if none of the above works, the symbol can be
            // translated as uninterpreted function
            // or predicate. The idea is, that if a formula is valid
            // with a interpreted function,
            // it has to be valid with an uninterpreted.
            // Caution: Counterexamples might be affected by this.
            return translateUnknown(term, quantifiedVars, services);
        }
    }

    private StringBuilder translateAsBindingUninterpretedPredicate(Term term, Function fun,
            List<QuantifiableVariable> quantifiedVars, ImmutableArray<Term> subs,
            Services services) throws IllegalFormulaException {

        ArrayList<StringBuilder> subterms = new ArrayList<>();
        for (int i = 0; i < term.arity(); i++) {
            if (!fun.bindVarsAt(i)) {
                Term sub = term.sub(i);
                // make type casts, if neccessary
                StringBuilder subterm = translateTerm(sub, quantifiedVars, services);
                if (this.isMultiSorted()) {
                    subterm = this.castIfNeccessary(subterm, sub.sort(), fun.argSort(i), services);
                }
                subterms.add(subterm);
            }
        }

        // check whether an equal term was already used.
        Term used = null;
        for (Term t : uninterpretedBindingPredicateNames.keySet()) {
            boolean termsMatch = ((t.op() == term.op()) && (t.arity() == term.arity()));
            for (int i = 0; i < t.arity(); i++) {
                // the terms only have to match on those positions where functions are defined
                if (fun.bindVarsAt(i)) {
                    termsMatch = termsMatch && t.sub(i).equalsModRenaming(term.sub(i));
                }
            }

            // the terms also match, if the entire sequence matches
            termsMatch = (termsMatch || t.equalsModRenaming(term));

            if (termsMatch) {
                used = t;
            }
        }
        if (used != null) {
            // The term was aready used. reuse the function name.

            // add the free variables in the term to the bound functions as parameter
            for (int i = 0; i < term.arity(); i++) {
                if (fun.bindVarsAt(i)) {
                    Iterator<QuantifiableVariable> iter = term.sub(i).freeVars().iterator();
                    // do not add those bound by the top level operator
                    ImmutableArray<QuantifiableVariable> qv = term.boundVars();
                    while (iter.hasNext()) {
                        QuantifiableVariable fv = iter.next();
                        boolean isBound = false;
                        for (QuantifiableVariable temp : qv) {
                            isBound = isBound || temp.equals(fv);
                        }
                        if (!isBound) {
                            subterms.add(0, translateVariable(fv));
                        }
                    }
                }
            }

            return translateFunction(uninterpretedBindingPredicateNames.get(used), subterms);
        } else {
            // create a new functionname
            StringBuilder newName = null;
            int i = 0;
            boolean alreadyContains = true;
            while (alreadyContains) {
                i++;
                newName = new StringBuilder("bindp_" + fun.name().toString() + "_" + i);
                alreadyContains = false;
                for (StringBuilder s : uninterpretedBindingPredicateNames.values()) {
                    alreadyContains = alreadyContains || s.toString().equals(newName.toString());
                }
            }

            // add the free variables in the term to the bound functions as parameter
            for (int j = 0; j < term.arity(); j++) {
                if (fun.bindVarsAt(j)) {
                    Iterator<QuantifiableVariable> iter = term.sub(j).freeVars().iterator();
                    // do not add those bound by the top level operator
                    ImmutableArray<QuantifiableVariable> qv = term.boundVars();
                    while (iter.hasNext()) {
                        QuantifiableVariable fv = iter.next();
                        boolean isBound = false;
                        for (QuantifiableVariable temp : qv) {
                            isBound = isBound || temp.equals(fv);
                        }
                        if (!isBound) {
                            subterms.add(0, translateVariable(fv));
                        }
                    }
                }
            }

            // add the function
            uninterpretedBindingPredicateNames.put(term, newName);
            // translate the new function
            return translatePredicate(newName, subterms);
        }
    }

    /**
     * Translate an uninterpreted function, which binds variables
     *
     * @param term The term with the binding function on top level
     * @param fun the function operator
     * @param quantifiedVars
     * @param subs the subterms of the function
     * @param services
     * @return A StringBuilder representing the translation of the function.
     * @throws IllegalFormulaException
     */
    private StringBuilder translateAsBindingUninterpretedFunction(Term term, Function fun,
            List<QuantifiableVariable> quantifiedVars, ImmutableArray<Term> subs,
            Services services) throws IllegalFormulaException {

        ArrayList<StringBuilder> subterms = new ArrayList<>();
        for (int i = 0; i < term.arity(); i++) {
            if (!fun.bindVarsAt(i)) {
                Term sub = term.sub(i);
                // make type casts, if neccessary
                StringBuilder subterm = translateTerm(sub, quantifiedVars, services);
                if (this.isMultiSorted()) {
                    subterm = this.castIfNeccessary(subterm, sub.sort(), fun.argSort(i), services);
                }
                subterms.add(subterm);
            }
        }

        // check whether an equal term was already used.
        Term used = null;
        for (Term t : uninterpretedBindingFunctionNames.keySet()) {
            boolean termsMatch = ((t.op() == term.op()) && (t.arity() == term.arity()));
            for (int i = 0; i < t.arity(); i++) {
                // the terms only have to match on those positions where functions are defined
                if (fun.bindVarsAt(i)) {
                    termsMatch = termsMatch && t.sub(i).equalsModRenaming(term.sub(i));
                }
            }

            // the terms also match, if the entire terms match
            termsMatch = (termsMatch || t.equalsModRenaming(term));

            if (termsMatch) {
                used = t;
            }
        }
        if (used != null) {
            // The term was aready used. reuse the function name.
            // add the free variables in the term to the bound functions as parameter
            for (int i = 0; i < term.arity(); i++) {
                if (fun.bindVarsAt(i)) {
                    Iterator<QuantifiableVariable> iter = term.sub(i).freeVars().iterator();
                    // do not add those bound by the top level operator
                    ImmutableArray<QuantifiableVariable> qv = term.boundVars();
                    while (iter.hasNext()) {
                        QuantifiableVariable fv = iter.next();
                        boolean isBound = false;
                        for (QuantifiableVariable temp : qv) {
                            isBound = isBound || temp.equals(fv);
                        }
                        if (!isBound) {
                            subterms.add(0, translateVariable(fv));
                        }
                    }
                }
            }


            return translateFunction(uninterpretedBindingFunctionNames.get(used), subterms);
        } else {
            // create a new functionname
            StringBuilder newName = null;
            int i = 0;
            boolean alreadyContains = true;
            while (alreadyContains) {
                i++;
                newName = new StringBuilder("bindf_" + fun.name().toString() + "_" + i);
                alreadyContains = false;
                for (StringBuilder s : uninterpretedBindingFunctionNames.values()) {
                    alreadyContains = alreadyContains || s.toString().equals(newName.toString());
                }
            }
            // add the free variables of the bound terms as parameter
            for (int j = 0; j < term.arity(); j++) {
                if (fun.bindVarsAt(j)) {
                    Iterator<QuantifiableVariable> iter = term.sub(j).freeVars().iterator();
                    // do not add those bound by the top level operator
                    ImmutableArray<QuantifiableVariable> qv = term.boundVars();
                    while (iter.hasNext()) {
                        QuantifiableVariable fv = iter.next();
                        boolean isBound = false;
                        for (QuantifiableVariable temp : qv) {
                            isBound = isBound || temp.equals(fv);
                        }
                        if (!isBound) {
                            subterms.add(0, translateVariable(fv));
                        }
                    }
                }
            }

            // add the function
            uninterpretedBindingFunctionNames.put(term, newName);
            // translate the new function
            return translateFunction(newName, subterms);
        }
    }

    private StringBuilder translateAsUninterpretedFunction(Function fun,
            List<QuantifiableVariable> quantifiedVars, ImmutableArray<Term> subs,
            Services services) throws IllegalFormulaException {
        // an uninterpreted function. just
        // translate it as such
        // it has to be made a difference between binding functions and those not binding

        ArrayList<StringBuilder> subterms = new ArrayList<>();
        int i = 0;
        for (Term sub : subs) {
            // make type casts, if neccessary
            StringBuilder subterm = translateTerm(sub, quantifiedVars, services);
            if (this.isMultiSorted()) {
                subterm = this.castIfNeccessary(subterm, sub.sort(), fun.argSort(i), services);
            }
            subterms.add(subterm);
            i++;
        }

        this.addFunction(fun, getArgSorts(fun), fun.sort(), services);

        return translateFunc(fun, subterms);
    }

    private boolean isNumberSymbol(Services services, Operator op) {
        return op == services.getTypeConverter().getIntegerLDT().getNumberSymbol();
    }

    private boolean isComplexMultiplication(Services services, Term t1, Term t2) {
        return !isNumberSymbol(services, t1.op()) && !isNumberSymbol(services, t2.op());

    }

    /**
     * This StringBuilder is used as predicate name for casts from int-valued to u-valued obects
     */
    private StringBuilder castPredicate;

    /**
     * This method adds a type cast to a translated formula, if neccessary. It is neccesary, if the
     * formula is of some int sort, but some not-int sort is expected. In this case add the type
     * cast.
     *
     * In general, it is also neccesary to add a type cast, if the formula has some non-int sort and
     * some int sort is expected. But this should never happen, as ever possible translation is made
     * with int-sort.
     *
     * A type-cast is never neccessary, if the translation can make use of multisort.
     *
     * @param formula The formula, that was translated.
     * @param formulaSort The sort, the translatet formula has.
     * @param targetSort The sort, the translated formula is expected to have.
     * @return A StringBuilder containing a type cast, if neccessary.
     */
    private StringBuilder castIfNeccessary(StringBuilder formula, Sort formulaSort, Sort targetSort,
            Services services) {
        if (!this.isMultiSorted()) {
            return formula;
        }
        if (isSomeIntegerSort(formulaSort, services) && !isSomeIntegerSort(targetSort, services)) {
            return this.cast(formula);
        } else if (!isSomeIntegerSort(formulaSort, services)
                && isSomeIntegerSort(targetSort, services)) {
            throw new RuntimeException("Error while translation.\n"
                + "Not possible to perform a typecast\n" + "for the formula " + formula + "\n"
                + "from type " + formulaSort.toString() + "\n" + "to type " + targetSort.toString()
                + "\n" + "Heavy internal error. Notify the administrator of the KeY tool.");
        } else {
            return formula;
        }
    }

    /**
     * Cast a formula of type int to type u. This cast is only performed, if multisort is not
     * suppoerted
     *
     * @param formula the formula to cast.
     * @return the casted formula.
     */
    private StringBuilder cast(StringBuilder formula) {
        if (this.castPredicate == null) {
            this.castPredicate = this.translateFunctionName(new StringBuilder("castInt2U"));
        }
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(formula);
        return this.translatePredicate(this.castPredicate, args);
    }

    /**
     * Get a predicate representing a modality. Make sure that equal modalities return the same
     * predicate.
     *
     * @param t The term representing the modality.
     * @param quantifiedVars quantified variables.
     * @param services the services object to use.
     * @return a unique predicate representing a modality.
     */
    private StringBuilder getModalityPredicate(Term t, List<QuantifiableVariable> quantifiedVars,
            Services services) throws IllegalFormulaException {
        // check, if the modality was already translated.
        for (Term toMatch : modalityPredicates.keySet()) {
            if (toMatch.equalsModRenaming(t)) {
                return modalityPredicates.get(toMatch);
            }
        }

        // if the program comes here, term has to be translated.

        // Collect all free Variable in the term
        final ImmutableSet<QuantifiableVariable> freeVars = t.freeVars();
        QuantifiableVariable[] args = freeVars.toArray(new QuantifiableVariable[freeVars.size()]);
        Term[] subs = new Term[args.length];
        Sort[] argsorts = new Sort[args.length];
        TermBuilder tb = services.getTermBuilder();
        for (int i = 0; i < args.length; i++) {
            QuantifiableVariable qv = args[i];
            if (qv instanceof LogicVariable) {
                LogicVariable lv = (LogicVariable) qv;
                subs[i] = tb.var(lv);
                argsorts[i] = lv.sort();
            } else {
                LOGGER.error("Schema variable found in formula.");
            }
        }
        // invent a new predicate
        Function fun = new Function(new Name("modConst"), t.sort(), argsorts);

        // Build the final predicate
        Term temp = tb.func(fun, subs);

        // translate the predicate
        StringBuilder cstr = this.translateTerm(temp, quantifiedVars, services);

        modalityPredicates.put(t, cstr);

        return cstr;

    }

    /**
     * Add an interpreted function to the set of special functions. Caution: If added here, make
     * sure to handle the function in getSpecialSortPredicates()
     *
     * @param fun the interpreted function to be added.
     */
    private void addSpecialFunction(Function fun) {
        specialFunctions.add(fun);
    }

    /**
     * Get the type predicate for the given sort and the given expression.
     *
     * @param s The sort, the type predicate is wanted for.
     * @param arg The expression, whose type should be defined.
     * @return The well formed type predicate expression.
     */
    protected StringBuilder getTypePredicate(Sort s, StringBuilder arg) {
        ArrayList<StringBuilder> arguments = new ArrayList<>();
        arguments.add(arg);
        return this.translatePredicate(typePredicates.get(s), arguments);
    }

    /**
     * Takes care of sequent tree parts that were not matched in translate(term, skolemization). In
     * this class it just produces a warning, nothing more. It is provided as a hook for subclasses.
     *
     * @param term The Term given to translate
     * @throws IllegalFormulaException
     */
    protected final StringBuilder translateUnknown(Term term,
            List<QuantifiableVariable> quantifiedVars, Services services)
            throws IllegalFormulaException {

        // translate the term as uninterpreted function/predicate
        Operator op = term.op();
        if (term.sort() == Sort.FORMULA) {
            // predicate
            LOGGER.debug("Translated as uninterpreted predicate: {}", term);
            ArrayList<StringBuilder> subterms = new ArrayList<>();
            for (int i = 0; i < op.arity(); i++) {
                subterms.add(translateTerm(term.sub(i), quantifiedVars, services));
            }
            ArrayList<Sort> sorts = new ArrayList<>();
            for (int i = 0; i < op.arity(); i++) {
                sorts.add(term.sub(i).sort());
            }
            this.addPredicate(op, sorts, services);

            return translatePred(op, subterms);
        } else {
            // function
            LOGGER.debug("Translated as uninterpreted function: {}", term);
            ArrayList<StringBuilder> subterms = new ArrayList<>();
            for (int i = 0; i < op.arity(); i++) {
                subterms.add(translateTerm(term.sub(i), quantifiedVars, services));
            }
            ArrayList<Sort> sorts = new ArrayList<>();
            for (int i = 0; i < op.arity(); i++) {
                if (term.sub(i).sort() != Sort.FORMULA) {
                    sorts.add(term.sub(i).sort());
                } else {
                    sorts.add(Sort.FORMULA);
                }
            }
            this.addFunction(op, sorts, term.sort(), services);

            return translateFunc(op, subterms);
        }
    }

    protected final StringBuilder translateVariable(Operator op) {
        if (usedVariableNames.containsKey(op)) {
            return usedVariableNames.get(op);
        } else {
            StringBuilder var = this.translateLogicalVar(new StringBuilder(op.name().toString()));
            usedVariableNames.put(op, var);
            return var;
        }
    }

    /**
     * translate a function.
     *
     * @param o the Operator used for this function.
     * @param sub The StringBuilders representing the arguments of this Function.
     * @return a StringBuilder representing the complete Function.
     */
    protected final StringBuilder translateFunc(Operator o, ArrayList<StringBuilder> sub) {
        StringBuilder name;
        if (usedFunctionNames.containsKey(o)) {
            name = usedFunctionNames.get(o);
        } else {
            name = translateFunctionName(new StringBuilder(o.name().toString()));
            usedFunctionNames.put(o, name);
            if (o instanceof Function) {
                usedFunctions.add(new FunctionWrapper(name, (Function) o));
            }
        }
        return translateFunction(name, sub);
    }

    /**
     * translate a bsum function. Alos add the created functionsymbol created depending on the term.
     *
     * @param bsumterm The term used as third argument of the bsum function.
     * @pram sub The two terms used as first and second argument of the bsum operator.
     * @return
     */
    protected final StringBuilder translateBsumFunction(Term bsumterm,
            ArrayList<StringBuilder> sub) {
        StringBuilder name = null;
        for (Term t : usedBsumTerms.keySet()) {
            if (t.equalsModRenaming(bsumterm)) {
                name = usedBsumTerms.get(t);
            }
        }
        if (name == null) {
            // the term wasnt used yet. Create a new functionsymbol
            int i = -1;
            boolean alreadyContains = true;
            while (alreadyContains) {
                i++;
                alreadyContains = false;
                for (StringBuilder s : usedBsumTerms.values()) {
                    if (s.toString().equals(BSUM_STRING + i)) {
                        alreadyContains = true;
                        break;
                    }
                }
            }
            name = new StringBuilder(BSUM_STRING + i);
            usedBsumTerms.put(bsumterm, name);
        }

        return translateFunction(name, sub);
    }


    /**
     * translate a bprod function. Alos add the created functionsymbol created depending on the
     * term.
     *
     * @param bprodterm The term used as third argument of the bsum function.
     * @pram sub The two terms used as first and second argument of the bsum operator.
     * @return
     */
    protected final StringBuilder translateBprodFunction(Term bprodterm,
            ArrayList<StringBuilder> sub) {
        StringBuilder name = null;
        for (Term t : usedBprodTerms.keySet()) {
            if (t.equalsModRenaming(bprodterm)) {
                name = usedBprodTerms.get(t);
            }
        }
        if (name == null) {
            // the term wasnt used yet. Create a new functionsymbol
            int i = -1;
            boolean alreadyContains = true;
            while (alreadyContains) {
                i++;
                alreadyContains = false;
                for (StringBuilder s : usedBprodTerms.values()) {
                    if (s.toString().equals(BPROD_STRING + i)) {
                        alreadyContains = true;
                        break;
                    }
                }
            }
            name = new StringBuilder(BPROD_STRING + i);
            usedBprodTerms.put(bprodterm, name);
        }

        return translateFunction(name, sub);
    }

    /**
     *
     * @param op the operator used for this function.
     * @param sorts the list of sort parameter of this function
     * @result the function's result sort
     */
    private void addFunction(Operator op, ArrayList<Sort> sorts, Sort result, Services services) {
        if (!this.functionDecls.containsKey(op)) {
            sorts.add(result);
            this.functionDecls.put(op, sorts);
            // add all sorts
            for (Sort s : sorts) {
                this.translateSort(s, services);
            }
        }
    }

    private void addPredicate(Operator op, ArrayList<Sort> sorts, Services services) {
        if (!this.predicateDecls.containsKey(op)) {
            this.predicateDecls.put(op, sorts);
            // add all sorts
            for (Sort s : sorts) {
                this.translateSort(s, services);
            }
        }
    }

    /**
     * Translate a predicate.
     *
     * @param o the operator used for this predicate.
     * @param sub The terms representing the arguments.
     * @return a StringBuilder representing the complete predicate.
     */
    private final StringBuilder translatePred(Operator o, ArrayList<StringBuilder> sub) {
        StringBuilder name;
        if (usedPredicateNames.containsKey(o)) {
            name = usedPredicateNames.get(o);
        } else {
            name = translatePredicateName(new StringBuilder(o.name().toString()));
            usedPredicateNames.put(o, name);
        }
        return translatePredicate(name, sub);
    }

    private final StringBuilder translateSort(Sort s, Services services) {
        if (usedDisplaySort.containsKey(s)) {
            return usedDisplaySort.get(s);
        } else {
            StringBuilder sortname =
                this.translateSort(s.name().toString(), isSomeIntegerSort(s, services));
            StringBuilder displaysort;

            if (!this.isMultiSorted()) {
                displaysort = this.getIntegerSort();
            } else {
                if (isSomeIntegerSort(s, services)) {
                    displaysort = this.getIntegerSort();
                } else {
                    displaysort = this.standardSort;
                }
            }

            StringBuilder realsort = sortname;

            usedDisplaySort.put(s, displaysort);
            usedRealSort.put(s, realsort);
            addTypePredicate(realsort, s);

            return displaysort;
        }
    }

    /**
     * Create a type predicate for a given sort.
     *
     * @param sortname the name, that should be used for the sort.
     * @param s the sort, this predicate belongs to.
     */
    private void addTypePredicate(StringBuilder sortname, Sort s) {
        if (!this.typePredicates.containsKey(s)) {
            StringBuilder predName = new StringBuilder("type_of_");
            predName.append(sortname);
            predName = this.translatePredicateName(predName);
            this.typePredicates.put(s, predName);
        }
    }

    protected boolean isSomeIntegerSort(Sort s, Services services) {
        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
        return s == integerSort;
    }



    private StringBuilder removeIllegalChars(StringBuilder template, ArrayList<String> toReplace,
            ArrayList<String> replacement) {
        // replace one String
        for (int i = 0; i < toReplace.size(); i++) {
            String toRep = toReplace.get(i);
            String replace = replacement.get(i);
            int index = template.indexOf(toRep);
            while (index >= 0) {
                template.replace(index, index + toRep.length(), replace);
                index = template.indexOf(toRep);
            }
        }

        return template;
    }


    protected StringBuilder makeUnique(StringBuilder name) {
        StringBuilder toReturn = new StringBuilder(name);

        // build the replacement pairs
        ArrayList<String> toReplace = new ArrayList<>();
        ArrayList<String> replacement = new ArrayList<>();

        toReplace.add("[]");
        replacement.add("_Array");

        toReplace.add("<");
        replacement.add("_abo_");

        toReplace.add(">");
        replacement.add("_abc_");

        toReplace.add("{");
        replacement.add("_cbo_");

        toReplace.add("}");
        replacement.add("_cbc_");

        toReplace.add(".");
        replacement.add("_dot_");

        toReplace.add(":");
        replacement.add("_col_");

        toReplace.add("\\");
        replacement.add("_");

        toReplace.add("$");
        replacement.add("_dollar_");

        toReturn = this.removeIllegalChars(toReturn, toReplace, replacement);
        // names are must not begin with special characters

        if (!('A' <= toReturn.charAt(0) && toReturn.charAt(0) <= 'Z')
                && !('a' <= toReturn.charAt(0) && toReturn.charAt(0) <= 'z')) {
            toReturn = (new StringBuilder()).append("a_").append(toReturn);
        }

        toReturn.append("_").append(nameCounter);
        nameCounter++;
        return toReturn;
    }



    /**
     * Translates the list <code>tacletFormulae</code> to the given syntax.
     *
     * @param services used for <code>translateTerm</code>
     */
    public ArrayList<StringBuilder> translateTaclets(Services services, SMTSettings settings)
            throws IllegalFormulaException {
        Collection<Taclet> taclets = settings.getTaclets();

        ArrayList<StringBuilder> result = new ArrayList<>();
        if (!settings.makesUseOfTaclets() || taclets == null || taclets.isEmpty()) {
            return result;
        }

        tacletSetTranslation = new DefaultTacletSetTranslation(services, settings);


        List<QuantifiableVariable> vector = new ArrayList<>();
        ImmutableSet<Sort> sorts = DefaultImmutableSet.nil();
        HashSet<Sort> tempSorts = new LinkedHashSet<>(usedRealSort.keySet());

        for (Operator op : usedFunctionNames.keySet()) {

            if (op instanceof SortDependingFunction) {
                Sort s = ((SortDependingFunction) op).getSortDependingOn();
                tempSorts.add(s);
            }
            if (op instanceof LocationVariable) {
                LocationVariable lv = (LocationVariable) op;
                if (lv.getContainerType() != null) {
                    tempSorts.add(lv.getContainerType().getSort());
                }

            }
        }

        for (Sort sort : tempSorts) {
            HeapLDT ldt = services.getTypeConverter().getHeapLDT();
            // Several special sorts should not be added to the collection
            if (ldt.getHeap().sort() != sort && ldt.getFieldSort() != sort
                    && services.getJavaInfo().nullSort() != sort && Sort.FORMULA != sort) {
                sorts = sorts.add(sort);
            }
        }
        for (TacletFormula tf : tacletSetTranslation.getTranslation(sorts)) {

            for (Term subterm : tf.getInstantiations()) {
                try {
                    StringBuilder term = translateComment(1, tf.getTaclet().displayName() + ":\n");

                    term.append(translateTerm(subterm, vector, services));

                    result.add(term);

                } catch (Throwable e) {

                    exceptionsForTacletTranslation.add(new RuntimeException(
                        "Could not translate taclet " + tf.getTaclet().name(), e));
                }

            }

        }

        return result;
    }

    protected StringBuilder translateComment(int newLines, String comment) {
        return new StringBuilder();
    }

    /**
     * Returns the maximum number that is supported by the solver. This limit is only considered if
     * <code>hasNumberLimit</code> returns <code>true</code>.
     */
    private long getMaxNumber() {
        return smtSettings.getMaximumInteger();
    }

    /**
     * Returns the minimum number that is supported by the solver. This limit is only considered if
     * <code>hasNumberLimit</code> returns <code>true</code>.
     */
    private long getMinNumber() {
        return smtSettings.getMinimumInteger();
    }
}
