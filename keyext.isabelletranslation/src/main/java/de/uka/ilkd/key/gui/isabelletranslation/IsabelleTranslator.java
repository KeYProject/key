package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

import java.io.IOException;
import java.util.*;

import static de.uka.ilkd.key.smt.SMTProblem.sequentToTerm;

public class IsabelleTranslator {

    private static final String LINE_ENDING = "\n";

    public IsabelleTranslator(Services services) {
    }

    public final StringBuilder translateProblem(Sequent sequent, Services services) throws IllegalFormulaException {
        Term problem = sequentToTerm(sequent, services);
        // TODO find correct values
        IsabelleMasterHandler masterHandler;
        try {
            masterHandler = new IsabelleMasterHandler(services, new String[0], new String[0]);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        List<Throwable> exceptions = masterHandler.getExceptions();
        if (!exceptions.isEmpty()) {
            StringBuilder message = new StringBuilder();
            for (Throwable t : exceptions) {
                message.append(t.getMessage()).append(System.lineSeparator());
            }
            throw new RuntimeException(message.toString());
        }

        StringBuilder formula = masterHandler.translate(problem);

        StringBuilder result = new StringBuilder();
        result.append("theory Translation imports Main begin").append(LINE_ENDING);

        for (StringBuilder preamble : masterHandler.getPreambles()) {
            result.append(LINE_ENDING).append(preamble).append(LINE_ENDING);
        }

        Set<Sort> extraParentsToCheck = new HashSet<>();
        extraParentsToCheck.add(Sort.ANY);
        extraParentsToCheck.add(services.getNamespaces().sorts().lookup("java.lang.Object"));

        Map<Sort, Set<Sort>> sortParentsMap = getSortsParents(masterHandler.getExtraSorts(), extraParentsToCheck);
        for (Sort sort : sortParentsMap.keySet()) {
            String sortName = getSortName(sort);
            String UNIV = sortName + "_UNIV";

            result.append("(* generated declaration for sort: ").append(sort.name().toString()).append(" *)").append(LINE_ENDING);
            result.append("lemma ex_").append(UNIV).append(":");
            result.append(getUnivSpec(sortParentsMap.get(sort), "{bottom}")).append(LINE_ENDING);
            result.append("  by simp").append(LINE_ENDING).append(LINE_ENDING);


            result.append("consts").append(LINE_ENDING).append(UNIV).append("::\"any set\"").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("specification (").append(UNIV).append(") ");
            result.append(getUnivSpec(sortParentsMap.get(sort), UNIV)).append(LINE_ENDING);
            result.append("  using ex_").append(UNIV).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING);


            String UNIV_spec_lemma_name = UNIV + "_specification";
            result.append("lemma ").append(UNIV_spec_lemma_name).append(":").append(getUnivSpec(sortParentsMap.get(sort), UNIV)).append(LINE_ENDING);
            result.append("  by (metis (mono_tags, lifting) ").append(UNIV).append("_def someI_ex ex_").append(UNIV).append(")").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("typedef ").append(sortName).append(" = \"").append(UNIV).append("\"").append(LINE_ENDING);
            String repName = sortName + "2any";
            String absName = "any2" + sortName;

            result.append("  morphisms ").append(repName).append(" ").append(absName).append(LINE_ENDING);
            result.append("  using ").append(UNIV_spec_lemma_name).append(" by auto").append(LINE_ENDING).append(LINE_ENDING);

            result.append("declare [[coercion ").append(repName).append("]]").append(LINE_ENDING).append(LINE_ENDING);

            result.append("lemma ").append(sortName).append("_type_specification[simp]:").append(getUnivSpec(sortParentsMap.get(sort), "(UNIV::" + sortName + " set)")).append(LINE_ENDING);
            result.append("  using ").append(UNIV_spec_lemma_name).append(" using type_definition.Rep_range type_definition_").append(sortName).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING).append(LINE_ENDING);

            for (Sort parentSort : sortParentsMap.get(sort)) {
                if (parentSort == Sort.ANY) {
                    continue;
                }
                String parentSortName = getSortName(parentSort);
                String parentSortInj = sortName + "2" + parentSortName;
                result.append(LINE_ENDING).append("abbreviation \"").append(parentSortInj).append(" \\<equiv> ");
                result.append("any2").append(parentSortName).append(" \\<circ> ").append(repName).append("\"").append(LINE_ENDING);

                result.append("declare [[coercion ").append(parentSortInj).append("]]").append(LINE_ENDING).append(LINE_ENDING);
            }

            result.append("instantiation ").append(sortName).append("::any").append(LINE_ENDING);
            result.append("begin").append(LINE_ENDING);
            result.append("definition \"to_any_").append(sortName).append(" \\<equiv> ").append(repName).append("\"").append(LINE_ENDING);
            result.append("definition \"cast_").append(sortName).append(" \\<equiv> ").append(absName).append("\"").append(LINE_ENDING);
            result.append("instance by standard").append(LINE_ENDING);
            result.append("end").append(LINE_ENDING);

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

        result.append("theorem solve: \"");
        result.append(formula).append("\"");
        result.append(LINE_ENDING).append(LINE_ENDING);
        result.append("(* Solve here *)").append(LINE_ENDING);

        return result.append("end").append(LINE_ENDING).append("end");
    }

    static String getSortName(Sort sort) {
        String name = sort.name().toString();
        return name.replace("[]", "arr").replace(".", "_");
    }

    private static String getUnivSpec(Set<Sort> parents, String insert) {
        List<String> parentSortNames = new ArrayList<>(parents.stream().map(IsabelleTranslator::getSortName).toList());
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
