/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

/**
 * Translator for Isabelle.
 */
public class IsabelleTranslator {
    /**
     * Line ending to use in translations
     */
    private static final String LINE_ENDING = "\n";

    /**
     * Services object used to initiate handlers
     */
    private final Services services;
    /**
     * The null sort
     */
    private final Sort nullSort;

    public IsabelleTranslator(Services services) {
        this.services = services;
        nullSort = services.getNamespaces().sorts().lookup("Null");
    }

    /**
     * Translates the given goal.
     *
     * @param goal goal to translate
     * @return IsabelleProblem containing the translation
     * @throws IllegalFormulaException if translation fails
     */
    public final IsabelleProblem translateProblem(Goal goal) throws IllegalFormulaException {
        Sequent sequent = goal.sequent();
        List<Term> antecedents =
            sequent.antecedent().asList().stream().map(SequentFormula::formula).toList();
        List<Term> succedents =
            sequent.succedent().asList().stream().map(SequentFormula::formula).toList();
        IsabelleMasterHandler masterHandler;
        try {
            masterHandler = new IsabelleMasterHandler(services, new String[0], new String[0]);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        List<StringBuilder> antecedentTranslations =
            antecedents.stream().map(masterHandler::translate).toList();
        List<StringBuilder> succedentTranslations =
            new ArrayList<>(succedents.stream().map(masterHandler::translate).toList());

        List<Throwable> exceptions = masterHandler.getExceptions();
        if (!exceptions.isEmpty()) {
            StringBuilder message = new StringBuilder();
            for (Throwable t : exceptions) {
                message.append(t.getMessage()).append(System.lineSeparator());
            }
            throw new IllegalFormulaException(message.toString());
        }


        // Construction of translation preamble
        StringBuilder translationPreamble = new StringBuilder();
        translationPreamble.append(
            "theory TranslationPreamble imports Main \"HOL-Combinatorics.List_Permutation\" begin")
                .append(LINE_ENDING);

        for (StringBuilder preamble : masterHandler.getPreambles()) {
            translationPreamble.append(LINE_ENDING).append(preamble).append(LINE_ENDING);
        }
        translationPreamble.append("end");


        // Construct translation theory
        StringBuilder translationTheory =
            new StringBuilder(IsabelleTranslationSettings.getInstance().getHeader())
                    .append(LINE_ENDING);

        // Find the sorts present on sequent to add definitions for sorts not in preamble
        Map<Sort, Set<Sort>> sortParentsMap =
            getSortsParents(masterHandler.getExtraSorts(), masterHandler.getPredefinedSorts());
        Map<Sort, Boolean> sortImplemented = new HashMap<>();
        sortParentsMap.keySet().forEach((Sort sort) -> sortImplemented.put(sort, false));
        masterHandler.getPredefinedSorts().forEach((Sort sort) -> sortImplemented.put(sort, true));

        Queue<Sort> sortImplementationQueue = new LinkedList<>(sortParentsMap.keySet());
        addSortsDefinitions(translationTheory, sortImplementationQueue, sortImplemented,
            sortParentsMap, masterHandler);



        // Construct proof locale
        translationTheory.append("locale varsAndFunctions");
        List<StringBuilder> locales = masterHandler.getLocales();

        // used for formatting
        boolean locale_empty = true;

        // add any supplementary locales like integer operation locale
        if (!locales.isEmpty()) {
            translationTheory.append(" = ");
            translationTheory.append(locales.remove(0));
            locale_empty = false;
        }
        for (StringBuilder locale : locales) {
            translationTheory.append(" + ").append(locale);
        }

        // Add declarations for variables present on sequent that are not in preamble
        Collection<String> variableDeclarations = masterHandler.getVariableDeclarations();
        if (!variableDeclarations.isEmpty() && locale_empty) {
            translationTheory.append(" = ");
            translationTheory.append(locales.remove(0));
            locale_empty = false;
        } else if (!variableDeclarations.isEmpty()) {
            translationTheory.append(" + ").append(LINE_ENDING);
        }
        for (String variableDecl : variableDeclarations) {
            translationTheory.append(LINE_ENDING).append(variableDecl);
        }
        translationTheory.append(LINE_ENDING);

        // Add assumption, that all field values are distinct. This is based on the KeY book
        if (!masterHandler.getNewFields().isEmpty()) {
            translationTheory.append("assumes distinct_fields:");
            translationTheory.append(getDistinctFieldLemma(masterHandler.getNewFields()));
            translationTheory.append(LINE_ENDING);
        }

        // This did not seem helpful from my testing, would add the assumption, that all sorts are
        // disjunct
        // sequentTranslation.append(getDistinctExtraSortsAssumptions(masterHandler));

        translationTheory.append("begin").append(LINE_ENDING);


        // Add proof theorem
        translationTheory.append("theorem solve: ");
        for (int i = 0; i < antecedentTranslations.size(); i++) {
            StringBuilder antecedentFormula = antecedentTranslations.get(i);
            translationTheory.append(LINE_ENDING).append("assumes antecedent_").append(i)
                    .append(":\"").append(antecedentFormula).append("\"");
        }
        translationTheory.append(LINE_ENDING);
        translationTheory.append("shows \"");
        if (succedentTranslations.isEmpty()) {
            translationTheory.append("False");
        } else {
            translationTheory.append(succedentTranslations.get(0));
        }
        for (int i = 1; i < succedentTranslations.size(); i++) {
            StringBuilder succedentFormula = succedentTranslations.get(i);
            translationTheory.append(LINE_ENDING).append("\\<or>").append(succedentFormula);
        }
        translationTheory.append("\"");

        return new IsabelleProblem(goal, translationPreamble.toString(),
            translationTheory.toString());
    }

    /**
     * Creates an assumption, that all sorts are disjunct (mod null).
     *
     * @param masterHandler masterHandler that handled translation
     * @return assumption, that sorts are disjunct
     */
    private StringBuilder getDistinctExtraSortsAssumptions(IsabelleMasterHandler masterHandler) {
        Set<Sort> sorts = masterHandler.getExtraSorts();
        Queue<Sort> sortsCheckQueue = new LinkedList<>(sorts);
        StringBuilder sortsAssumptions = new StringBuilder();

        while (!sortsCheckQueue.isEmpty()) {
            Sort s = sortsCheckQueue.remove();
            if (s == JavaDLTheory.ANY || s == JavaDLTheory.FORMULA) {
                continue;
            }
            String sType = masterHandler.translateSortName(s) + "_type";
            String sVal = "(" + masterHandler.translateSortName(s) + "\\<^sub>v\\<^sub>a\\<^sub>l::"
                + masterHandler.translateSortName(s) + ")";
            for (Sort s2 : sortsCheckQueue) {
                if (s2 == JavaDLTheory.ANY || s2 == JavaDLTheory.FORMULA) {
                    continue;
                }
                if (!s.extendsTrans(s2) && !s2.extendsTrans(s)) {
                    String s2Type = masterHandler.translateSortName(s2) + "_type";
                    String s2Val =
                        "(" + masterHandler.translateSortName(s2) + "\\<^sub>v\\<^sub>a\\<^sub>l::"
                            + masterHandler.translateSortName(s2) + ")";
                    if (nullSort.extendsTrans(s) && nullSort.extendsTrans(s2)) {
                        sortsAssumptions.append("assumes disjointModNull_")
                                .append(masterHandler.translateSortName(s)).append("_")
                                .append(masterHandler.translateSortName(s2))
                                .append(":\"").append(sVal).append(" = ").append(s2Val)
                                .append("\\<Longrightarrow> s=null\"").append(LINE_ENDING);
                    } else {
                        // Sorts are unrelated. need to add distinctness assumption
                        sortsAssumptions.append("assumes \"disjointTypes ").append(sType)
                                .append(" ").append(s2Type).append("\"").append(LINE_ENDING);
                    }
                }
            }
        }
        return sortsAssumptions;
    }

    /**
     * Lemma to show fields are distinct
     *
     * @param newFields the list of translations of field variables
     * @return a lemma stating the distinctness of all field variables
     */
    private StringBuilder getDistinctFieldLemma(Collection<StringBuilder> newFields) {
        if (newFields.isEmpty())
            return new StringBuilder();
        String commaSeparatedFields = String.join(",", newFields);
        StringBuilder distinctFieldLemma = new StringBuilder();
        distinctFieldLemma.append("\"(distinct [");
        distinctFieldLemma.append(commaSeparatedFields);
        distinctFieldLemma.append(", created]) \\<and> (({");
        distinctFieldLemma.append(commaSeparatedFields);
        distinctFieldLemma.append(", created} \\<inter> image arr (UNIV::int set)) = {})\"");
        return distinctFieldLemma;
    }

    /**
     * Adds the definitions for the given sorts to the given translation theory.
     * Works recursively using the queue of sorts to be implemented
     *
     * @param translationTheory {@link StringBuilder} containing the translation theory up to this
     *        point
     * @param sortImplementationQueue queue for the implementation of sorts
     * @param sortImplemented Map to check whether a sort has been implemented
     * @param sortParentsMap Map, mapping a sort to the set of its parents
     * @param masterHandler the masterHandler used during translation
     */
    private void addSortsDefinitions(StringBuilder translationTheory,
            Queue<Sort> sortImplementationQueue, Map<Sort, Boolean> sortImplemented,
            Map<Sort, Set<Sort>> sortParentsMap, IsabelleMasterHandler masterHandler) {
        if (sortImplementationQueue.isEmpty()) {
            return;
        }

        // Ensure that a sort is not implemented before its parents
        // Instead push it to the end of the queue
        Sort sort = sortImplementationQueue.poll();
        for (Sort parent : sortParentsMap.get(sort)) {
            if (!sortImplemented.get(parent)) {
                sortImplementationQueue.add(sort);
                addSortsDefinitions(translationTheory, sortImplementationQueue, sortImplemented,
                    sortParentsMap, masterHandler);
                return;
            }
        }

        // Ensure an array sort is not implemented before its elementsort
        if ((sort instanceof ArraySort) && !sortImplemented.get(((ArraySort) sort).elementSort())) {
            sortImplementationQueue.add(sort);
            addSortsDefinitions(translationTheory, sortImplementationQueue, sortImplemented,
                sortParentsMap, masterHandler);
            return;
        }


        // Add generated declaration
        String sortName = masterHandler.translateSortName(sort);
        String UNIV = sortName + "_UNIV";

        translationTheory.append("(* generated declaration for sort: ")
                .append(sort.name()).append(" *)").append(LINE_ENDING);
        // Lemma showing there is at least one element in this sort
        translationTheory.append("lemma ex_").append(UNIV).append(":");
        translationTheory.append(getUnivSpec(masterHandler, sortParentsMap.get(sort), "{bottom}"))
                .append(LINE_ENDING);
        translationTheory.append("  by simp").append(LINE_ENDING).append(LINE_ENDING);

        // Introduce the universe of this sort
        translationTheory.append("consts").append(LINE_ENDING).append(UNIV).append("::\"any set\"")
                .append(LINE_ENDING);
        translationTheory.append(LINE_ENDING);

        // Use specification to specify the properties of the universe of this sort (subset of
        // parents)
        translationTheory.append("specification (").append(UNIV).append(") ");
        translationTheory.append(getUnivSpec(masterHandler, sortParentsMap.get(sort), UNIV))
                .append(LINE_ENDING);
        translationTheory.append("  using ex_").append(UNIV).append(" by blast")
                .append(LINE_ENDING);
        translationTheory.append(LINE_ENDING);


        // Reformulate specification as lemma for easier use by Isabelle
        String UNIV_spec_lemma_name = UNIV + "_specification";
        translationTheory.append("lemma ").append(UNIV_spec_lemma_name).append(":")
                .append(getUnivSpec(masterHandler, sortParentsMap.get(sort), UNIV))
                .append(LINE_ENDING);
        translationTheory.append("  by (metis (mono_tags, lifting) ").append(UNIV)
                .append("_def someI_ex ex_").append(UNIV).append(")").append(LINE_ENDING);
        translationTheory.append(LINE_ENDING);

        // Defines this sort as a new type in Isabelle based on the established universe
        translationTheory.append("typedef ").append(sortName).append(" = \"").append(UNIV)
                .append("\"").append(LINE_ENDING);
        String repName = sortName + "2any";
        String absName = "any2" + sortName;

        // Add morphisms that map between the sort and the any sort
        translationTheory.append("  morphisms ").append(repName).append(" ").append(absName)
                .append(LINE_ENDING);
        translationTheory.append("  using ").append(UNIV_spec_lemma_name).append(" by auto")
                .append(LINE_ENDING).append(LINE_ENDING);

        // Add coercions for Isabelle to use coercive subtyping
        translationTheory.append("declare [[coercion ").append(repName).append("]]")
                .append(LINE_ENDING).append(LINE_ENDING);

        // Repeat properties of type for UNIV constants of Isabelle
        // Improves performance and shortens proofs. Used in schema
        String IsabelleTypeUniverseOfSort = "(UNIV::" + sortName + " set)";
        translationTheory.append("lemma ").append(sortName).append("_type_specification[simp]:")
                .append(getUnivSpec(masterHandler, sortParentsMap.get(sort),
                    IsabelleTypeUniverseOfSort))
                .append(LINE_ENDING);
        translationTheory.append("  using ").append(UNIV_spec_lemma_name)
                .append(" using type_definition.Rep_range type_definition_").append(sortName)
                .append(" by blast").append(LINE_ENDING);
        translationTheory.append(LINE_ENDING).append(LINE_ENDING);

        // extra coercions for all other parent types
        // may lead to extra performance if left out, because Isabelle will only need to deal with
        // comparisons in any
        for (Sort parentSort : sortParentsMap.get(sort)) {
            if (parentSort == JavaDLTheory.ANY) {
                continue;
            }
            String parentSortName = masterHandler.translateSortName(parentSort);
            String parentSortInj = sortName + "2" + parentSortName;
            translationTheory.append(LINE_ENDING).append("fun ").append(parentSortInj)
                    .append(" where \"").append(parentSortInj)
                    .append(" x = ").append("any2").append(parentSortName).append(" (")
                    .append(repName).append(" x)\"").append(LINE_ENDING);
            translationTheory.append("declare [[coercion ").append(parentSortInj).append("]]")
                    .append(LINE_ENDING).append(LINE_ENDING);
        }

        // Instantiation of any typeclass for this sort
        // the typeclass provides polymorphisms for the cast functions
        translationTheory.append("instantiation ").append(sortName).append("::any")
                .append(LINE_ENDING);
        translationTheory.append("begin").append(LINE_ENDING);
        String to_any_fun_Name = "to_any_" + sortName;
        translationTheory.append("fun ").append(to_any_fun_Name)
                .append(" where \"").append(to_any_fun_Name).append(" x = ").append(repName)
                .append(" x\"")
                .append(LINE_ENDING);
        String cast_fun_Name = "cast_" + sortName;
        translationTheory.append("fun ").append(cast_fun_Name)
                .append("  where \"").append(cast_fun_Name).append(" x = ").append(absName)
                .append(" x\"")
                .append(LINE_ENDING);
        translationTheory.append("instance by standard").append(LINE_ENDING);
        translationTheory.append("end").append(LINE_ENDING).append(LINE_ENDING);

        // coercion of null sort to this sort
        if (nullSort.extendsTrans(sort)) {
            String null_to_sort_name = "Null2" + sortName;
            translationTheory.append("fun ").append(null_to_sort_name).append(" where \"")
                    .append(null_to_sort_name)
                    .append(" x = ").append(absName).append("(Null2any x)\"").append(LINE_ENDING);
            translationTheory.append("declare [[coercion Null2").append(sortName).append("]]")
                    .append(LINE_ENDING).append(LINE_ENDING);
        }

        // Instantiation of array typeclass, which provides polymorphism for element type
        if (sort instanceof ArraySort) {
            translationTheory.append("instantiation ").append(sortName).append("::array")
                    .append(LINE_ENDING);
            translationTheory.append("begin").append(LINE_ENDING);

            String element_type_name = "element_type_" + sortName;
            String elementSortName =
                masterHandler.translateSortName(((ArraySort) sort).elementSort());
            String elementSortType =
                "Abs_javaDL_type ((UNIV::" + elementSortName + " set)::any set)";
            translationTheory.append("fun ").append(element_type_name)
                    .append(" where \"").append(element_type_name)
                    .append(" (x::").append(sortName).append(")").append(" = ")
                    .append(elementSortType).append("\"")
                    .append(LINE_ENDING);

            translationTheory.append("instance by standard").append(LINE_ENDING);
            translationTheory.append("end").append(LINE_ENDING).append(LINE_ENDING);
        }

        // Constant representing the sort as a Abs_javaDL_type value
        String typeConstName = sortName + "_type";
        translationTheory.append("definition \"").append(typeConstName)
                .append(" = Abs_javaDL_type ").append(IsabelleTypeUniverseOfSort).append("\"");

        translationTheory.append(LINE_ENDING).append(LINE_ENDING);

        sortImplemented.put(sort, true);
        addSortsDefinitions(translationTheory, sortImplementationQueue, sortImplemented,
            sortParentsMap, masterHandler);
    }

    /**
     * Creates the statement about the properties of the universe of a sort. Subset of the universes
     * of its parents
     *
     * @param masterHandler masterhandler used during translation
     * @param parents parent sorts of the sort
     * @param insert name of the universe constant
     * @return the statement about the properties of the universe of a sort
     */
    private static String getUnivSpec(IsabelleMasterHandler masterHandler, Set<Sort> parents,
            String insert) {
        List<String> parentSortNames =
            new ArrayList<>(parents.stream().map(masterHandler::translateSortName).toList());
        StringBuilder univSpec = new StringBuilder();
        if (parentSortNames.isEmpty()) {
            parentSortNames.add("any");
        }
        univSpec.append("\"").append(insert).append(" \\<subseteq> (UNIV::")
                .append(parentSortNames.get(0)).append(" set)");
        for (int i = 1; i < parentSortNames.size(); i++) {
            univSpec.append(" \\<and> ").append(insert).append(" \\<subseteq> (UNIV::")
                    .append(parentSortNames.get(i)).append(" set)");
        }
        univSpec.append(" \\<and> bottom \\<in> ").append(insert).append("\"");
        return univSpec.toString();
    }

    private static Map<Sort, Set<Sort>> getSortsParents(Set<Sort> sorts, Set<Sort> outsideParents) {
        // may want to avoid some of the looping over sorts by presorting?
        HashMap<Sort, Set<Sort>> result = new HashMap<>();
        for (Sort sort : sorts) {
            Set<Sort> parents = new HashSet<>();
            for (Sort sort2 : sorts) {
                if (!sort.equals(sort2) && sort.extendsTrans(sort2)) {
                    parents.add(sort2);
                }
            }
            for (Sort sort2 : outsideParents) {
                if (!sort.equals(sort2) && sort.extendsTrans(sort2)) {
                    parents.add(sort2);
                }
            }
            result.put(sort, parents);
        }
        return result;
    }
}
