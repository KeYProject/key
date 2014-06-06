// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.conditions.TypeComparisonCondition;
import de.uka.ilkd.key.rule.conditions.TypeComparisonCondition.Mode;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.SkeletonGenerator;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletTranslator;

interface VariablePool {
        LogicVariable getInstantiationOfLogicVar(Sort instantiation,
                        LogicVariable lv);

        LogicVariable getLogicVariable(Name name, Sort sort);
}

public class AssumptionGenerator implements TacletTranslator, VariablePool {

        // only for testing.
        // private boolean appendGenericTerm = false;


        protected HashMap<String, LogicVariable> usedVariables = new LinkedHashMap<String, LogicVariable>();

        protected Collection<TranslationListener> listener = new LinkedList<TranslationListener>();

        protected TacletConditions conditions;
        private Services services;

        private GenericTranslator genericTranslator = new GenericTranslator(
                        this);

        public AssumptionGenerator(Services services) {
                this.services = services;

        }

        public TacletFormula translate(Taclet t, ImmutableSet<Sort> sorts,
                        int maxGeneric) throws IllegalTacletException {

                // determine the variable conditions.
                this.conditions = new TacletConditions(t);

                // translate the taclet, but do not translate generic
                // // variables
                // // and do not quantify the variables.

                Term term = SkeletonGenerator.DEFAULT_TACLET_TRANSLATOR.translate(t, services);

                // rebuild the term to exchange schema variables with logic
                // varibales.
                term = rebuildTerm(term);

                Collection<Term> result = new LinkedList<Term>();
                result.add(term);

                Collection<Term> result2 = new LinkedList<Term>();

                // step: quantify all free variables.
                for (Term te : result) {
                        te = quantifyTerm(te, services);
                        result2.add(te);
                }

                // step: translate the generics sorts.
                result = new LinkedList<Term>();
                for (Term te : result2) {
                        result.addAll(genericTranslator.translate(te, sorts, t,
                                        conditions, services, maxGeneric));
                }

                return new AssumptionFormula(t, result, "", conditions);

        }

        /**
         * Use this method to rebuild the given term. The method splits the term
         * in its single components and assemblies them. After every splitting
         * step the method calls <code>changeTerm</code>. This mechanism can be
         * used to exchange subterms.
         * 
         * @param term
         *                the term to rebuild.
         * @return returns the new term.
         */

        private Term rebuildTerm(Term term) {

                Term[] subTerms = new Term[term.arity()];

            ImmutableArray<QuantifiableVariable> variables = term.boundVars();
                for (int i = 0; i < term.arity(); i++) {
                     
                        subTerms[i] = rebuildTerm(term.sub(i));
                       

                }

                term = services.getTermFactory().createTerm(term.op(), subTerms, 
                                                            variables, JavaBlock.EMPTY_JAVABLOCK);
          
                term = changeTerm(term);
           
                if (term.op() instanceof Quantifier) {
                        for (QuantifiableVariable qv : variables) {
                                for (TranslationListener l : listener) {
                                        l.eventQuantifiedVariable(qv);
                                }
                        }
                }

                return term;
        }
        
        @SuppressWarnings("unused") // this method is only for testing, and is not used normally.
        private void print(Term term){
                System.out.println(term.op().name());
                System.out.println(term.op().getClass());
                System.out.println(term.sort());
        }

        public LogicVariable getInstantiationOfLogicVar(Sort instantiation,
                        LogicVariable lv) {

                LogicVariable res = getLogicVariable(new Name(instantiation
                                .name().toString()
                                + "__"
                                + lv.name().toString()), instantiation);
                for (TranslationListener l : listener) {
                        l.eventSort(instantiation);
                }
                return res;
        }

        static public boolean isAbstractOrInterface(Sort sort, Services services) {
                if (!isReferenceSort(sort, services))
                        return false;
                return sort.isAbstract();

        }

        static public boolean isReferenceSort(Sort sort, Services services) {
                return (sort.extendsTrans(services.getJavaInfo().objectSort()) && !(sort instanceof NullSort));

        }

        static public HashSet<GenericSort> collectGenerics(Term term) {
                HashSet<GenericSort> genericSorts = new LinkedHashSet<GenericSort>();
                collectGenerics(term, genericSorts);
                return genericSorts;
        }

        static private void collectGenerics(Term term,
                        HashSet<GenericSort> genericSorts) {

                if (term.op() instanceof SortDependingFunction) {
                        SortDependingFunction func = (SortDependingFunction) term
                                        .op();
                        if (func.getSortDependingOn() instanceof GenericSort) {
                                genericSorts.add((GenericSort) func
                                                .getSortDependingOn());
                        }
                }

                if (term.sort() instanceof GenericSort) {
                        genericSorts.add((GenericSort) term.sort());
                }
                for (int i = 0; i < term.arity(); i++) {
                        collectGenerics(term.sub(i), genericSorts);
                }

        }

        /**
         * Creates an array containing objectCount^bucketCount rows. Each of
         * this rows has bucketCount columns. The method enumerates all possible
         * variations of putting <code>objectCount</code> different objects into
         * <code>bucketCount</code> buckets.<br>
         * Example<br>
         * For <code>objects= 2</code> and <code>bucket =3</code> the method
         * returns:<br>
         * 000<br>
         * 001<br>
         * 010<br>
         * 011<br>
         * 100<br>
         * 101<br>
         * 110<br>
         * 111<br>
         * 
         * @param objectCount
         *                the number of objects.
         * @param bucketCount
         *                the number of buckets.
         * @return an array of dimension objectCount^bucketCount x bucketCount
         */
        static public byte[][] generateReferenceTable(int objectCount,
                        int bucketCount) {

                int colCount = bucketCount;
                int rowCount = (int) Math.pow(objectCount, bucketCount);
                byte max = (byte) ((byte) objectCount - 1);

                byte table[][] = new byte[rowCount][colCount];

                for (int r = 1; r < rowCount; r++) {
                        int temp = 1;
                        for (int c = 0; c < colCount; c++) {
                                byte newVal = (byte) (table[r - 1][c] + temp);
                                if (newVal > max) {
                                        newVal = 0;
                                        temp = 1;
                                } else {
                                        temp = 0;
                                }
                                table[r][c] = newVal;

                        }

                }

                return table;
        }

        /**
         * Checks the referenceTable whether there are rows that are not
         * allowed. For example: the notSame-Condition is hurted.
         * 
         */
        static public void checkTable(byte[][] referenceTable,
                        Sort[] instTable, Sort[] genericTable,
                        TacletConditions conditions, Services services) {

                for (int r = 0; r < referenceTable.length; r++) {
                        for (int c = 0; c < referenceTable[r].length; c++) {
                                int index = referenceTable[r][c];
                                if (referenceTable[r][0] == -1)
                                        break;

                                if ((conditions.containsIsReferenceCondition(genericTable[c]) > 0 && !isReferenceSort(
                                                instTable[index], services))
                                                || (conditions.containsAbstractInterfaceCondition(genericTable[c]) && !isAbstractOrInterface(
                                                                instTable[index],
                                                                services))
                                                || (conditions.containsNotAbstractInterfaceCondition(genericTable[c]) && isAbstractOrInterface(
                                                                instTable[index],
                                                                services))
                                                || (!conditions.containsIsSubtypeRelation(
                                                                genericTable[c],
                                                                instTable[index],
                                                                Mode.IS_SUBTYPE))

                                                || (!conditions.containsIsSubtypeRelation(
                                                                genericTable[c],
                                                                instTable[index],
                                                                Mode.NOT_IS_SUBTYPE))

                                                || (!isReferenceSort(
                                                                instTable[index],
                                                                services) && isReferenceSort(
                                                                genericTable[c],
                                                                services))

                                )

                                {
                                        referenceTable[r][0] = -1;
                                        break;

                                }
                                for (int c2 = c + 1; c2 < referenceTable[r].length; c2++) {
                                        int index2 = referenceTable[r][c2]; // not
                                                                            // same

                                        if ((conditions.containsNotSameCondition(
                                                        genericTable[c],
                                                        genericTable[c2]) && instTable[index]
                                                        .equals(instTable[index2]))
                                                        || //
                                                        (genericTable[c].extendsTrans(genericTable[c2]) && !instTable[index]
                                                                        .extendsTrans(instTable[index2]))
                                                        || (conditions.containsComparisionCondition(
                                                                        genericTable[c],
                                                                        genericTable[c2],
                                                                        TypeComparisonCondition.Mode.SAME) && !instTable[index]
                                                                        .equals(instTable[index2]))

                                                        || (conditions.containsComparisionCondition(
                                                                        genericTable[c],
                                                                        genericTable[c2],
                                                                        TypeComparisonCondition.Mode.IS_SUBTYPE) && !instTable[index]
                                                                        .extendsTrans(instTable[index2]))
                                                        || (conditions.containsComparisionCondition(
                                                                        genericTable[c],
                                                                        genericTable[c2],
                                                                        TypeComparisonCondition.Mode.IS_SUBTYPE) && !instTable[index2]
                                                                        .extendsTrans(instTable[index]))
                                                        || (conditions.containsComparisionCondition(
                                                                        genericTable[c],
                                                                        genericTable[c2],
                                                                        TypeComparisonCondition.Mode.NOT_IS_SUBTYPE) && instTable[index]
                                                                        .extendsTrans(instTable[index2]))
                                                        || (conditions.containsComparisionCondition(
                                                                        genericTable[c],
                                                                        genericTable[c2],
                                                                        TypeComparisonCondition.Mode.NOT_IS_SUBTYPE) && instTable[index2]
                                                                        .extendsTrans(instTable[index]))
                                                        || (genericTable[c]
                                                                        .extendsTrans(genericTable[c2]) && !instTable[index]
                                                                        .extendsTrans(instTable[index2]))
                                                        || (genericTable[c2]
                                                                        .extendsTrans(genericTable[c]) && !instTable[index2]
                                                                        .extendsTrans(instTable[index]))

                                        ) {
                                                referenceTable[r][0] = -1;
                                                break;
                                        }

                                }

                        }
                }

        }

        /**
         * Quantifies a term, i.d. every free variable is bounded by a
         * allquantor.
         * 
         * @param term
         *                the term to be quantify.
       * @param services TODO
         * @return the quantified term.
         */
        protected static Term quantifyTerm(Term term, TermServices services)
                        throws IllegalTacletException {
                TermBuilder tb = services.getTermBuilder();
                // Quantify over all free variables.
                for (QuantifiableVariable qv : term.freeVars()) {

                        if (!(qv instanceof LogicVariable)) {
                                throw new IllegalTacletException(
                                                "Error of translation: "
                                                                + "There is a free variable that is not of type LogicVariable: "
                                                                + qv);
                        }

                        term = tb.all(qv, term);

                }
                return term;
        }

        /**
         * Returns a new logic variable with the given name and sort. If already
         * a logic variable exists with the same name and sort this variable is
         * returned instead of a new logic variable.
         * 
         * @param name
         *                name of the logic variable.
         * @param sort
         *                sort of the logic variable.
         * @return logic variable with the given name and sort.
         */
        public LogicVariable getLogicVariable(Name name, Sort sort) {
                 name = new Name(eliminateSpecialChars(name.toString()));
    
                LogicVariable l = usedVariables.get(name.toString());
                if (l == null) {

                        l = new LogicVariable(name, sort);
                        usedVariables.put(name.toString(), l);
                }
    
                return l;

        }

        /**
         * eliminates all special chars.
         */
        static protected String eliminateSpecialChars(String name) {
                StringBuffer toReturn = new StringBuffer(name);

                // build the replacement pairs
                ArrayList<String> toReplace = new ArrayList<String>();
                ArrayList<String> replacement = new ArrayList<String>();

                toReplace.add("[]");
                replacement.add("_Array");

                toReplace.add(".");
                replacement.add("_dot_");

                toReplace.add(":");
                replacement.add("_col_");

                toReplace.add("#");
                replacement.add("_meta_");

                toReturn = removeIllegalChars(toReturn, toReplace, replacement);

                return toReturn.toString();
        }

        static private StringBuffer removeIllegalChars(StringBuffer template,
                        ArrayList<String> toReplace,
                        ArrayList<String> replacement) {
                // replace one String
                for (int i = 0; i < toReplace.size(); i++) {
                        String toRep = toReplace.get(i);
                        String replace = replacement.get(i);
                        int index = template.indexOf(toRep);
                        while (index >= 0) {
                                template.replace(index, index + toRep.length(),
                                                replace);
                                index = template.indexOf(toRep);
                        }
                }

                return template;
        }

        /**
         * Override this method if you want to change the term, i.e. exchanging
         * schema variables for logic variables. See <code>rebuildTerm</code>.
         * 
         * @param term
         *                the term to be changed.
         * @return the new term.
         */
        protected Term changeTerm(Term term) {

                TermBuilder tb = services.getTermBuilder();

                // translate schema variables into logical variables
                if (term.op() instanceof SchemaVariable) {
                        if (!term.sort().equals(Sort.FORMULA)) {
                                term = tb.var(getLogicVariable(
                                                term.op().name(), term.sort()));

                        }

                }

                // It can be that a quantifiable variable is not a logical
                // variable but a schema
                // variable. In this case the schema variable is replaced with a
                // logical variable.
                if (term.op() instanceof Quantifier) {
                        LinkedList<QuantifiableVariable> list = new LinkedList<QuantifiableVariable>();

                        for (QuantifiableVariable qv : term.varsBoundHere(0)) {
                                list.add(getLogicVariable(qv.name(), qv.sort()));
                        }

                        ImmutableArray<QuantifiableVariable> array = new ImmutableArray<QuantifiableVariable>(
                                        list);

                        term = services.getTermFactory().createTerm(term.op(),
                                        term.subs(), array,
                                        JavaBlock.EMPTY_JAVABLOCK,
                                        term.getLabels());

                }

                return term;
        }

        public void addListener(TranslationListener list) {
                genericTranslator.addListener(list);
                this.listener.add(list);
        }

        public void removeListener(TranslationListener list) {
                genericTranslator.removeListener(list);
                this.listener.remove(list);
        }

}