package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;

import java.io.IOException;
import java.util.*;

public class IsabelleTranslator {

    private static final String LINE_ENDING = "\n";

    private final Services services;

    public IsabelleTranslator(Services services) {
        this.services = services;
    }

    public final StringBuilder translateProblem(Sequent sequent) throws IllegalFormulaException {
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
            throw new RuntimeException(message.toString());
        }

        StringBuilder result = new StringBuilder();
        result.append("theory Translation imports Main begin").append(LINE_ENDING);

        for (StringBuilder preamble : masterHandler.getPreambles()) {
            result.append(LINE_ENDING).append(preamble).append(LINE_ENDING);
        }

        Sort nullSort = services.getNamespaces().sorts().lookup("Null");

        Map<Sort, Set<Sort>> sortParentsMap = getSortsParents(masterHandler.getExtraSorts(), masterHandler.getPredefinedSorts());
        for (Sort sort : sortParentsMap.keySet()) {
            String sortName = masterHandler.translateSortName(sort);
            String UNIV = sortName + "_UNIV";

            result.append("(* generated declaration for sort: ").append(sort.name().toString()).append(" *)").append(LINE_ENDING);
            result.append("lemma ex_").append(UNIV).append(":");
            result.append(getUnivSpec(masterHandler, sortParentsMap.get(sort), "{bottom}")).append(LINE_ENDING);
            result.append("  by simp").append(LINE_ENDING).append(LINE_ENDING);


            result.append("consts").append(LINE_ENDING).append(UNIV).append("::\"any set\"").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("specification (").append(UNIV).append(") ");
            result.append(getUnivSpec(masterHandler, sortParentsMap.get(sort), UNIV)).append(LINE_ENDING);
            result.append("  using ex_").append(UNIV).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING);


            String UNIV_spec_lemma_name = UNIV + "_specification";
            result.append("lemma ").append(UNIV_spec_lemma_name).append(":").append(getUnivSpec(masterHandler, sortParentsMap.get(sort), UNIV)).append(LINE_ENDING);
            result.append("  by (metis (mono_tags, lifting) ").append(UNIV).append("_def someI_ex ex_").append(UNIV).append(")").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("typedef ").append(sortName).append(" = \"").append(UNIV).append("\"").append(LINE_ENDING);
            String repName = sortName + "2any";
            String absName = "any2" + sortName;

            result.append("  morphisms ").append(repName).append(" ").append(absName).append(LINE_ENDING);
            result.append("  using ").append(UNIV_spec_lemma_name).append(" by auto").append(LINE_ENDING).append(LINE_ENDING);

            result.append("declare [[coercion ").append(repName).append("]]").append(LINE_ENDING).append(LINE_ENDING);


            String IsabelleTypeUniverseOfSort = "(UNIV::" + sortName + " set)";
            result.append("lemma ").append(sortName).append("_type_specification[simp]:")
                    .append(getUnivSpec(masterHandler, sortParentsMap.get(sort), IsabelleTypeUniverseOfSort))
                    .append(LINE_ENDING);
            result.append("  using ").append(UNIV_spec_lemma_name).append(" using type_definition.Rep_range type_definition_").append(sortName).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING).append(LINE_ENDING);

            for (Sort parentSort : sortParentsMap.get(sort)) {
                if (parentSort == Sort.ANY) {
                    continue;
                }
                String parentSortName = masterHandler.translateSortName(parentSort);
                String parentSortInj = sortName + "2" + parentSortName;
                result.append(LINE_ENDING).append("fun ").append(parentSortInj).append(" where \"").append(parentSortInj)
                        .append(" x = ").append("any2").append(parentSortName).append(" (").append(repName).append(" x)\"").append(LINE_ENDING);
                result.append("declare [[coercion ").append(parentSortInj).append("]]").append(LINE_ENDING).append(LINE_ENDING);
            }

            result.append("instantiation ").append(sortName).append("::any").append(LINE_ENDING);
            result.append("begin").append(LINE_ENDING);
            String to_any_fun_Name = "to_any_" + sortName;
            result.append("fun ").append(to_any_fun_Name)
                    .append(" where \"").append(to_any_fun_Name).append(" x = ").append(repName).append(" x\"")
                    .append(LINE_ENDING);
            String cast_fun_Name = "cast_" + sortName;
            result.append("fun ").append(cast_fun_Name)
                    .append("  where \"").append(cast_fun_Name).append(" x = ").append(absName).append(" x\"")
                    .append(LINE_ENDING);
            result.append("instance by standard").append(LINE_ENDING);
            result.append("end").append(LINE_ENDING).append(LINE_ENDING);

            if (nullSort.extendsTrans(sort)) {
                String null_to_sort_name = "Null2" + sortName;
                result.append("fun ").append(null_to_sort_name).append(" where \"").append(null_to_sort_name)
                        .append(" x = ").append(absName).append("(Null2any x)\"").append(LINE_ENDING);
                result.append("declare [[coercion Null2").append(sortName).append("]]").append(LINE_ENDING).append(LINE_ENDING);
            }

            if (sort instanceof ArraySort) {
                result.append("instantiation ").append(sortName).append("::array").append(LINE_ENDING);
                result.append("begin").append(LINE_ENDING);

                String element_type_name = "element_type_" + sortName;
                String elementSortName = masterHandler.translateSortName(((ArraySort) sort).elementSort());
                String elementSortType = "Abs_javaDL_type ((UNIV::" + elementSortName + " set)::any set)";
                result.append("fun ").append(element_type_name)
                        .append(" where \"").append(element_type_name)
                        .append(" (x::").append(sortName).append(")").append(" = ")
                        .append(elementSortType).append("\"")
                        .append(LINE_ENDING);

                result.append("instance by standard").append(LINE_ENDING);
                result.append("end").append(LINE_ENDING).append(LINE_ENDING);
            }

            String typeConstName = sortName + "_type";
            result.append("definition \"").append(typeConstName).append(" = Abs_javaDL_type ").append(IsabelleTypeUniverseOfSort).append("\"");

            result.append(LINE_ENDING).append(LINE_ENDING);
        }

        result.append("locale varsAndFunctions");
        List<StringBuilder> locales = masterHandler.getLocales();

        boolean locale_empty = true;

        if (!locales.isEmpty()) {
            result.append(" = ");
            result.append(locales.remove(0));
            locale_empty = false;
        }
        for (StringBuilder locale : locales) {
            result.append(" + ").append(locale);
        }

        List<StringBuilder> constDecls = masterHandler.getConstDeclarations();
        if (!constDecls.isEmpty() && locale_empty) {
            result.append(" = ");
            result.append(locales.remove(0));
            locale_empty = false;
        } else if (!locale_empty) {
            result.append(" + ").append(LINE_ENDING);
        }
        for (StringBuilder constDecl : constDecls) {
            result.append(LINE_ENDING).append(constDecl);
        }
        result.append(LINE_ENDING);


        result.append("begin").append(LINE_ENDING);

        result.append("theorem solve: ");
        for (int i = 0; i < antecedentTranslations.size(); i++) {
            StringBuilder antecedentFormula = antecedentTranslations.get(i);
            result.append(LINE_ENDING).append("assumes antecedent_").append(i).append(":\"").append(antecedentFormula).append("\"");
        }
        result.append(LINE_ENDING);
        result.append("shows \"").append(succedentTranslations.get(0));
        for (int i = 1; i < succedentTranslations.size(); i++) {

            StringBuilder succedentFormula = succedentTranslations.get(i);
            result.append(LINE_ENDING).append("\\<or>").append(succedentFormula);
        }
        result.append("\"");
        result.append(LINE_ENDING).append(LINE_ENDING);
        result.append("(* Solve here *)").append(LINE_ENDING);

        return result;
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
