/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.conditions.TypeComparisonCondition.Mode;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.SkeletonGenerator;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletTranslator;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

interface VariablePool {
    LogicVariable getInstantiationOfLogicVar(Sort instantiation, LogicVariable lv);

    LogicVariable getLogicVariable(Name name, Sort sort);
}


public class AssumptionGenerator implements TacletTranslator, VariablePool {
    protected final Map<String, LogicVariable> usedVariables = new LinkedHashMap<>();

    protected final Collection<TranslationListener> listener = new LinkedList<>();

    protected TacletConditions conditions;
    private final Services services;

    private final GenericTranslator genericTranslator = new GenericTranslator(this);

    public AssumptionGenerator(Services services) {
        this.services = services;

    }

    public TacletFormula translate(Taclet t, ImmutableSet<Sort> sorts, int maxGeneric)
            throws IllegalTacletException {

        // determine the variable conditions.
        this.conditions = new TacletConditions(t);

        // translate the taclet, but do not translate generic
        // // variables
        // // and do not quantify the variables.

        Term term = SkeletonGenerator.DEFAULT_TACLET_TRANSLATOR.translate(t, services);

        // rebuild the term to exchange schema variables with logic
        // varibales.
        term = rebuildTerm(term);

        Collection<Term> result = new LinkedList<>();
        result.add(term);

        Collection<Term> result2 = new LinkedList<>();

        // step: quantify all free variables.
        for (Term te : result) {
            te = quantifyTerm(te, services);
            result2.add(te);
        }

        // step: translate the generics sorts.
        result = new LinkedList<>();
        for (Term te : result2) {
            result.addAll(
                genericTranslator.translate(te, sorts, t, conditions, services, maxGeneric));
        }

        return new AssumptionFormula(t, result, "", conditions);

    }

    /**
     * Use this method to rebuild the given term. The method splits the term in its single
     * components and assemblies them. After every splitting step the method calls
     * <code>changeTerm</code>. This mechanism can be used to exchange subterms.
     *
     * @param term the term to rebuild.
     * @return returns the new term.
     */

    private Term rebuildTerm(Term term) {

        Term[] subTerms = new Term[term.arity()];

        ImmutableArray<QuantifiableVariable> variables = term.boundVars();
        for (int i = 0; i < term.arity(); i++) {

            subTerms[i] = rebuildTerm(term.sub(i));


        }

        term = services.getTermFactory().createTerm(term.op(), subTerms, variables, null);

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

    public LogicVariable getInstantiationOfLogicVar(Sort instantiation, LogicVariable lv) {
        LogicVariable res = getLogicVariable(
            new Name(instantiation.name().toString() + "__" + lv.name().toString()), instantiation);
        for (TranslationListener l : listener) {
            l.eventSort(instantiation);
        }
        return res;
    }

    public static boolean isAbstractOrInterface(Sort sort, Services services) {
        if (!isReferenceSort(sort, services)) {
            return false;
        }
        return sort.isAbstract();

    }

    public static boolean isReferenceSort(Sort sort, Services services) {
        return (sort.extendsTrans(services.getJavaInfo().objectSort())
                && !(sort instanceof NullSort));

    }

    public static Set<GenericSort> collectGenerics(Term term) {
        HashSet<GenericSort> genericSorts = new LinkedHashSet<>();
        collectGenerics(term, genericSorts);
        return genericSorts;
    }

    private static void collectGenerics(Term term, HashSet<GenericSort> genericSorts) {

        if (term.op() instanceof SortDependingFunction func) {
            if (func.getSortDependingOn() instanceof GenericSort) {
                genericSorts.add((GenericSort) func.getSortDependingOn());
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
     * Creates an array containing objectCount^bucketCount rows. Each of this rows has bucketCount
     * columns. The method enumerates all possible variations of putting <code>objectCount</code>
     * different objects into <code>bucketCount</code> buckets.<br>
     * Example<br>
     * For <code>objects= 2</code> and <code>bucket =3</code> the method returns:<br>
     * 000<br>
     * 001<br>
     * 010<br>
     * 011<br>
     * 100<br>
     * 101<br>
     * 110<br>
     * 111<br>
     *
     * @param objectCount the number of objects.
     * @param bucketCount the number of buckets.
     * @return an array of dimension objectCount^bucketCount x bucketCount
     */
    public static byte[][] generateReferenceTable(int objectCount, int bucketCount) {

        int rowCount = (int) Math.pow(objectCount, bucketCount);
        byte max = (byte) ((byte) objectCount - 1);

        byte[][] table = new byte[rowCount][bucketCount];

        for (int r = 1; r < rowCount; r++) {
            int temp = 1;
            for (int c = 0; c < bucketCount; c++) {
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
     * Checks the referenceTable whether there are rows that are not allowed. For example: the
     * notSame-Condition is hurted.
     */
    public static void checkTable(byte[][] referenceTable, Sort[] instTable, Sort[] genericTable,
            TacletConditions conditions, Services services) {

        for (int r = 0; r < referenceTable.length; r++) {
            for (int c = 0; c < referenceTable[r].length; c++) {
                int index = referenceTable[r][c];
                if (referenceTable[r][0] == -1) {
                    break;
                }

                final var a = conditions.containsIsReferenceCondition(genericTable[c]) > 0
                        && !isReferenceSort(instTable[index], services);
                final var b = conditions.containsAbstractInterfaceCondition(genericTable[c])
                        && !isAbstractOrInterface(instTable[index], services);
                final var g = conditions.containsNotAbstractInterfaceCondition(genericTable[c])
                        && isAbstractOrInterface(instTable[index], services);
                final var d = !conditions.containsIsSubtypeRelation(genericTable[c],
                    instTable[index], Mode.IS_SUBTYPE);
                final var e = !conditions.containsIsSubtypeRelation(genericTable[c],
                    instTable[index], Mode.NOT_IS_SUBTYPE);
                final var f = !isReferenceSort(instTable[index], services)
                        && isReferenceSort(genericTable[c], services);
                if (a || b || g || d || e || f) {
                    referenceTable[r][0] = -1;
                    break;

                }
                for (int c2 = c + 1; c2 < referenceTable[r].length; c2++) {
                    int index2 = referenceTable[r][c2]; // not
                    // same

                    final var b1 =
                        conditions.containsNotSameCondition(genericTable[c], genericTable[c2])
                                && instTable[index].equals(instTable[index2]);
                    final var b2 = genericTable[c].extendsTrans(genericTable[c2])
                            && !instTable[index].extendsTrans(instTable[index2]);
                    final var b3 = conditions.containsComparisionCondition(genericTable[c],
                        genericTable[c2], Mode.SAME) && !instTable[index].equals(instTable[index2]);
                    final var b4 =
                        conditions.containsComparisionCondition(genericTable[c], genericTable[c2],
                            Mode.IS_SUBTYPE) && !instTable[index].extendsTrans(instTable[index2]);
                    final var b5 =
                        conditions.containsComparisionCondition(genericTable[c], genericTable[c2],
                            Mode.IS_SUBTYPE) && !instTable[index2].extendsTrans(instTable[index]);
                    final var b6 = genericTable[c2].extendsTrans(genericTable[c])
                            && !instTable[index2].extendsTrans(instTable[index]);
                    final var b7 = conditions.containsComparisionCondition(genericTable[c],
                        genericTable[c2], Mode.NOT_IS_SUBTYPE)
                            && instTable[index2].extendsTrans(instTable[index]);
                    final var b8 = conditions.containsComparisionCondition(genericTable[c],
                        genericTable[c2], Mode.NOT_IS_SUBTYPE)
                            && instTable[index].extendsTrans(instTable[index2]);
                    if (b1 || b2 || b3 || b4 || b5 || b8 || b7 || b6) {
                        referenceTable[r][0] = -1;
                        break;
                    }
                }
            }
        }

    }

    /**
     * Quantifies a term, i.d. every free variable is bounded by a allquantor.
     *
     * @param term the term to be quantify.
     * @return the quantified term.
     */
    protected static Term quantifyTerm(Term term, TermServices services)
            throws IllegalTacletException {
        TermBuilder tb = services.getTermBuilder();
        // Quantify over all free variables.
        for (QuantifiableVariable qv : term.freeVars()) {

            if (!(qv instanceof LogicVariable)) {
                throw new IllegalTacletException("Error of translation: "
                    + "There is a free variable that is not of type LogicVariable: " + qv);
            }

            term = tb.all(qv, term);

        }
        return term;
    }

    /**
     * Returns a new logic variable with the given name and sort. If already a logic variable exists
     * with the same name and sort this variable is returned instead of a new logic variable.
     *
     * @param name name of the logic variable.
     * @param sort sort of the logic variable.
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
    protected static String eliminateSpecialChars(String name) {
        var toReturn = new StringBuilder(name);

        // build the replacement pairs
        ArrayList<String> toReplace = new ArrayList<>();
        ArrayList<String> replacement = new ArrayList<>();

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

    private static StringBuilder removeIllegalChars(StringBuilder template,
            ArrayList<String> toReplace, ArrayList<String> replacement) {
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

    /**
     * Override this method if you want to change the term, i.e. exchanging schema variables for
     * logic variables. See <code>rebuildTerm</code>.
     *
     * @param term the term to be changed.
     * @return the new term.
     */
    protected Term changeTerm(Term term) {

        TermBuilder tb = services.getTermBuilder();

        // translate schema variables into logical variables
        if (term.op() instanceof SchemaVariable && !term.sort().equals(JavaDLTheory.FORMULA)) {
            term = tb.var(getLogicVariable(term.op().name(), term.sort()));
        }

        // It can be that a quantifiable variable is not a logical
        // variable but a schema
        // variable. In this case the schema variable is replaced with a
        // logical variable.
        if (term.op() instanceof Quantifier) {
            LinkedList<QuantifiableVariable> list = new LinkedList<>();

            for (QuantifiableVariable qv : term.varsBoundHere(0)) {
                list.add(getLogicVariable(qv.name(), qv.sort()));
            }

            ImmutableArray<QuantifiableVariable> array = new ImmutableArray<>(list);

            term = services.getTermFactory().createTerm(term.op(), term.subs(), array,
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
