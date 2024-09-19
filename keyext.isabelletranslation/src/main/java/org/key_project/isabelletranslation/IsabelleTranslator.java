package org.key_project.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArraySort;
import org.key_project.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;

import java.io.IOException;
import java.util.*;

public class IsabelleTranslator {

    private static final String LINE_ENDING = "\n";

    private final Services services;

    private final Sort nullSort;

    public IsabelleTranslator(Services services) {
        this.services = services;
        nullSort = services.getNamespaces().sorts().lookup("Null");
    }

    public final IsabelleProblem translateProblem(Goal goal) throws IllegalFormulaException {
        Sequent sequent = goal.sequent();
        List<Term> antecedents = sequent.antecedent().asList().stream().map(SequentFormula::formula).toList();
        List<Term> succedents = sequent.succedent().asList().stream().map(SequentFormula::formula).toList();
        IsabelleMasterHandler masterHandler;
        try {
            masterHandler = new IsabelleMasterHandler(services, new String[0], new String[0]);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        List<StringBuilder> antecedentTranslations = antecedents.stream().map(masterHandler::translate).toList();
        List<StringBuilder> succedentTranslations = new ArrayList<>(succedents.stream().map(masterHandler::translate).toList());

        List<Throwable> exceptions = masterHandler.getExceptions();
        if (!exceptions.isEmpty()) {
            StringBuilder message = new StringBuilder();
            for (Throwable t : exceptions) {
                message.append(t.getMessage()).append(System.lineSeparator());
            }
            throw new IllegalFormulaException(message.toString());
        }

        StringBuilder translationPreamble = new StringBuilder();
        translationPreamble.append("theory TranslationPreamble imports Main \"HOL-Combinatorics.List_Permutation\" begin").append(LINE_ENDING);

        for (StringBuilder preamble : masterHandler.getPreambles()) {
            translationPreamble.append(LINE_ENDING).append(preamble).append(LINE_ENDING);
        }
        translationPreamble.append("end");

        StringBuilder sequentTranslation = new StringBuilder(IsabelleTranslationSettings.getInstance().getHeader()).append(LINE_ENDING);

        //TODO make this into a tree structure to avoid excessive looping (over sorts) | sort the implementation queue
        Map<Sort, Set<Sort>> sortParentsMap = getSortsParents(masterHandler.getExtraSorts(), masterHandler.getPredefinedSorts());
        Map<Sort, Boolean> sortImplemented = new HashMap<>();
        sortParentsMap.keySet().forEach((Sort sort) -> sortImplemented.put(sort, false));
        masterHandler.getPredefinedSorts().forEach((Sort sort) -> sortImplemented.put(sort, true));

        Queue<Sort> sortImplementationQueue = new LinkedList<>(sortParentsMap.keySet());
        addSortsDefinitions(sequentTranslation, sortImplementationQueue, sortImplemented, sortParentsMap, masterHandler);


        sequentTranslation.append("locale varsAndFunctions");
        List<StringBuilder> locales = masterHandler.getLocales();

        boolean locale_empty = true;

        if (!locales.isEmpty()) {
            sequentTranslation.append(" = ");
            sequentTranslation.append(locales.remove(0));
            locale_empty = false;
        }
        for (StringBuilder locale : locales) {
            sequentTranslation.append(" + ").append(locale);
        }

        Collection<String> constDecls = masterHandler.getConstDeclarations();
        if (!constDecls.isEmpty() && locale_empty) {
            sequentTranslation.append(" = ");
            sequentTranslation.append(locales.remove(0));
            locale_empty = false;
        } else if (!constDecls.isEmpty()) {
            sequentTranslation.append(" + ").append(LINE_ENDING);
        }
        for (String constDecl : constDecls) {
            sequentTranslation.append(LINE_ENDING).append(constDecl);
        }
        sequentTranslation.append(LINE_ENDING);

        if (!masterHandler.getNewFields().isEmpty()) {
            sequentTranslation.append("assumes distinct_fields:");
            sequentTranslation.append(getDistinctFieldLemma(masterHandler.getNewFields()));
            sequentTranslation.append(LINE_ENDING);
        }

        //This did not seem helpful from my testing
        //sequentTranslation.append(getDistinctExtraSortsAssumptions(masterHandler));

        sequentTranslation.append("begin").append(LINE_ENDING);

        sequentTranslation.append("theorem solve: ");
        for (int i = 0; i < antecedentTranslations.size(); i++) {
            StringBuilder antecedentFormula = antecedentTranslations.get(i);
            sequentTranslation.append(LINE_ENDING).append("assumes antecedent_").append(i).append(":\"").append(antecedentFormula).append("\"");
        }
        sequentTranslation.append(LINE_ENDING);
        sequentTranslation.append("shows \"");
        if (succedentTranslations.isEmpty()) {
            sequentTranslation.append("False");
        } else {
            sequentTranslation.append(succedentTranslations.get(0));
        }
        for (int i = 1; i < succedentTranslations.size(); i++) {

            StringBuilder succedentFormula = succedentTranslations.get(i);
            sequentTranslation.append(LINE_ENDING).append("\\<or>").append(succedentFormula);
        }
        sequentTranslation.append("\"");

        return new IsabelleProblem(goal, translationPreamble.toString(), sequentTranslation.toString());
    }

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
            String sVal = "(" + masterHandler.translateSortName(s) + "\\<^sub>v\\<^sub>a\\<^sub>l::" + masterHandler.translateSortName(s) + ")";
            for (Sort s2 : sortsCheckQueue) {
                if (s2 == JavaDLTheory.ANY || s2 == JavaDLTheory.FORMULA) {
                    continue;
                }
                if (!s.extendsTrans(s2) && !s2.extendsTrans(s)) {
                    String s2Type = masterHandler.translateSortName(s2) + "_type";
                    String s2Val = "(" + masterHandler.translateSortName(s2) + "\\<^sub>v\\<^sub>a\\<^sub>l::" + masterHandler.translateSortName(s2) + ")";
                    if (nullSort.extendsTrans(s) && nullSort.extendsTrans(s2)) {
                        sortsAssumptions.append("assumes disjointModNull_").append(masterHandler.translateSortName(s)).append("_").append(masterHandler.translateSortName(s2))
                                .append(":\"").append(sVal).append(" = ").append(s2Val).append("\\<Longrightarrow> s=null\"").append(LINE_ENDING);
                    } else {
                        //Sorts are unrelated. need to add distinctness assumption
                        sortsAssumptions.append("assumes \"disjointTypes ").append(sType).append(" ").append(s2Type).append("\"").append(LINE_ENDING);
                    }
                }
            }
        }
        return sortsAssumptions;
    }

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

    private void addSortsDefinitions(StringBuilder sequentTranslation, Queue<Sort> sortImplementationQueue, Map<Sort, Boolean> sortImplemented,
                                     Map<Sort, Set<Sort>> sortParentsMap, IsabelleMasterHandler masterHandler) {
        if (sortImplementationQueue.isEmpty()) {
            return;
        }

        Sort sort = sortImplementationQueue.poll();
        for (Sort parent : sortParentsMap.get(sort)) {
            if (!sortImplemented.get(parent)) {
                sortImplementationQueue.add(sort);
                addSortsDefinitions(sequentTranslation, sortImplementationQueue, sortImplemented, sortParentsMap, masterHandler);
                return;
            }
        }
        if ((sort instanceof ArraySort) && !sortImplemented.get(((ArraySort) sort).elementSort())) {
            sortImplementationQueue.add(sort);
            addSortsDefinitions(sequentTranslation, sortImplementationQueue, sortImplemented, sortParentsMap, masterHandler);
            return;
        }
        String sortName = masterHandler.translateSortName(sort);
        String UNIV = sortName + "_UNIV";

        sequentTranslation.append("(* generated declaration for sort: ").append(sort.name().toString()).append(" *)").append(LINE_ENDING);
        sequentTranslation.append("lemma ex_").append(UNIV).append(":");
        sequentTranslation.append(getUnivSpec(masterHandler, sortParentsMap.get(sort), "{bottom}")).append(LINE_ENDING);
        sequentTranslation.append("  by simp").append(LINE_ENDING).append(LINE_ENDING);


        sequentTranslation.append("consts").append(LINE_ENDING).append(UNIV).append("::\"any set\"").append(LINE_ENDING);
        sequentTranslation.append(LINE_ENDING);

        sequentTranslation.append("specification (").append(UNIV).append(") ");
        sequentTranslation.append(getUnivSpec(masterHandler, sortParentsMap.get(sort), UNIV)).append(LINE_ENDING);
        sequentTranslation.append("  using ex_").append(UNIV).append(" by blast").append(LINE_ENDING);
        sequentTranslation.append(LINE_ENDING);


        String UNIV_spec_lemma_name = UNIV + "_specification";
        sequentTranslation.append("lemma ").append(UNIV_spec_lemma_name).append(":").append(getUnivSpec(masterHandler, sortParentsMap.get(sort), UNIV)).append(LINE_ENDING);
        sequentTranslation.append("  by (metis (mono_tags, lifting) ").append(UNIV).append("_def someI_ex ex_").append(UNIV).append(")").append(LINE_ENDING);
        sequentTranslation.append(LINE_ENDING);

        sequentTranslation.append("typedef ").append(sortName).append(" = \"").append(UNIV).append("\"").append(LINE_ENDING);
        String repName = sortName + "2any";
        String absName = "any2" + sortName;

        sequentTranslation.append("  morphisms ").append(repName).append(" ").append(absName).append(LINE_ENDING);
        sequentTranslation.append("  using ").append(UNIV_spec_lemma_name).append(" by auto").append(LINE_ENDING).append(LINE_ENDING);

        sequentTranslation.append("declare [[coercion ").append(repName).append("]]").append(LINE_ENDING).append(LINE_ENDING);


        String IsabelleTypeUniverseOfSort = "(UNIV::" + sortName + " set)";
        sequentTranslation.append("lemma ").append(sortName).append("_type_specification[simp]:")
                .append(getUnivSpec(masterHandler, sortParentsMap.get(sort), IsabelleTypeUniverseOfSort))
                .append(LINE_ENDING);
        sequentTranslation.append("  using ").append(UNIV_spec_lemma_name).append(" using type_definition.Rep_range type_definition_").append(sortName).append(" by blast").append(LINE_ENDING);
        sequentTranslation.append(LINE_ENDING).append(LINE_ENDING);

        for (Sort parentSort : sortParentsMap.get(sort)) {
            if (parentSort == JavaDLTheory.ANY) {
                continue;
            }
            String parentSortName = masterHandler.translateSortName(parentSort);
            String parentSortInj = sortName + "2" + parentSortName;
            sequentTranslation.append(LINE_ENDING).append("fun ").append(parentSortInj).append(" where \"").append(parentSortInj)
                    .append(" x = ").append("any2").append(parentSortName).append(" (").append(repName).append(" x)\"").append(LINE_ENDING);
            sequentTranslation.append("declare [[coercion ").append(parentSortInj).append("]]").append(LINE_ENDING).append(LINE_ENDING);
        }

        sequentTranslation.append("instantiation ").append(sortName).append("::any").append(LINE_ENDING);
        sequentTranslation.append("begin").append(LINE_ENDING);
        String to_any_fun_Name = "to_any_" + sortName;
        sequentTranslation.append("fun ").append(to_any_fun_Name)
                .append(" where \"").append(to_any_fun_Name).append(" x = ").append(repName).append(" x\"")
                .append(LINE_ENDING);
        String cast_fun_Name = "cast_" + sortName;
        sequentTranslation.append("fun ").append(cast_fun_Name)
                .append("  where \"").append(cast_fun_Name).append(" x = ").append(absName).append(" x\"")
                .append(LINE_ENDING);
        sequentTranslation.append("instance by standard").append(LINE_ENDING);
        sequentTranslation.append("end").append(LINE_ENDING).append(LINE_ENDING);

        if (nullSort.extendsTrans(sort)) {
            String null_to_sort_name = "Null2" + sortName;
            sequentTranslation.append("fun ").append(null_to_sort_name).append(" where \"").append(null_to_sort_name)
                    .append(" x = ").append(absName).append("(Null2any x)\"").append(LINE_ENDING);
            sequentTranslation.append("declare [[coercion Null2").append(sortName).append("]]").append(LINE_ENDING).append(LINE_ENDING);
        }

        if (sort instanceof ArraySort) {
            sequentTranslation.append("instantiation ").append(sortName).append("::array").append(LINE_ENDING);
            sequentTranslation.append("begin").append(LINE_ENDING);

            String element_type_name = "element_type_" + sortName;
            String elementSortName = masterHandler.translateSortName(((ArraySort) sort).elementSort());
            String elementSortType = "Abs_javaDL_type ((UNIV::" + elementSortName + " set)::any set)";
            sequentTranslation.append("fun ").append(element_type_name)
                    .append(" where \"").append(element_type_name)
                    .append(" (x::").append(sortName).append(")").append(" = ")
                    .append(elementSortType).append("\"")
                    .append(LINE_ENDING);

            sequentTranslation.append("instance by standard").append(LINE_ENDING);
            sequentTranslation.append("end").append(LINE_ENDING).append(LINE_ENDING);
        }

        String typeConstName = sortName + "_type";
        sequentTranslation.append("definition \"").append(typeConstName).append(" = Abs_javaDL_type ").append(IsabelleTypeUniverseOfSort).append("\"");

        sequentTranslation.append(LINE_ENDING).append(LINE_ENDING);

        sortImplemented.put(sort, true);
        addSortsDefinitions(sequentTranslation, sortImplementationQueue, sortImplemented, sortParentsMap, masterHandler);
    }

    private static String getUnivSpec(IsabelleMasterHandler masterHandler, Set<Sort> parents, String insert) {
        List<String> parentSortNames = new ArrayList<>(parents.stream().map(masterHandler::translateSortName).toList());
        StringBuilder univSpec = new StringBuilder();
        if (parentSortNames.isEmpty()) {
            parentSortNames.add("any");
        }
        univSpec.append("\"").append(insert).append(" \\<subseteq> (UNIV::").append(parentSortNames.get(0)).append(" set)");
        for (int i = 1; i < parentSortNames.size(); i++) {
            univSpec.append(" \\<and> ").append(insert).append(" \\<subseteq> (UNIV::").append(parentSortNames.get(i)).append(" set)");
        }
        univSpec.append(" \\<and> bottom \\<in> ").append(insert).append("\"");
        return univSpec.toString();
    }

    private static Map<Sort, Set<Sort>> getSortsParents(Set<Sort> sorts, Set<Sort> outsideParents) {
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
