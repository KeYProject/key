package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProblem.sequentToTerm;

public class IsabelleTranslator {

    private final HashMap<Sort, StringBuilder> usedSorts = new HashMap<>();

    private final HashMap<Function, StringBuilder> usedFunctions = new HashMap<>();

    private final HashMap<Function, StringBuilder> usedPredicates = new HashMap<>();

    private static final StringBuilder FALSESTRING = new StringBuilder("False");

    private static final StringBuilder TRUESTRING = new StringBuilder("True");

    private static final StringBuilder ALLSTRING = new StringBuilder("\\<forall>");

    private static final StringBuilder EXISTSTRING = new StringBuilder("\\<exists>");

    private static final StringBuilder ANDSTRING = new StringBuilder("\\<and>");

    private static final StringBuilder ORSTRING = new StringBuilder("\\<or>");

    private static final StringBuilder NOTSTRING = new StringBuilder("\\<not>");

    private static final StringBuilder EQSTRING = new StringBuilder("=");

    private static final StringBuilder IMPLYSTRING = new StringBuilder("-->");


    private static final String LINE_ENDING = "\n";

    public IsabelleTranslator(Services services) {
        //TODO add intrinsic sorts and functions that shouldnt be overridden
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
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
        StringBuilder formula = masterHandler.translate(problem);

        StringBuilder result = new StringBuilder();
        result.append("theory Translation imports Main begin").append(LINE_ENDING);

        for (StringBuilder preamble : masterHandler.getPreambles()) {
            result.append(LINE_ENDING).append(preamble).append(LINE_ENDING);
        }

        for (Sort sort : masterHandler.getExtraSorts()) {
            String sortName = sort.name().toString();
            String UNIV = sortName + "_UNIV";
            //TODO ensure that parent sorts are already known or not included

            result.append("(* generated declaration for sort: ").append(sort.name().toString()).append(" *)").append(LINE_ENDING);
            result.append("lemma ex_").append(UNIV).append(":");
            result.append(getUnivSpec(services, sort, "{bottom}")).append(LINE_ENDING);
            result.append("  by simp").append(LINE_ENDING).append(LINE_ENDING);


            result.append("consts").append(LINE_ENDING).append(UNIV).append("::\"any set\"").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("specification (").append(UNIV).append(") ");
            result.append(getUnivSpec(services, sort, UNIV)).append(LINE_ENDING);
            result.append("  using ex_").append(UNIV).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING);

            //TODO needs other lemmata
            String UNIV_spec_lemma_name = UNIV + "_specification";
            result.append("lemma ").append(UNIV_spec_lemma_name).append(":").append(getUnivSpec(services, sort, UNIV)).append(LINE_ENDING);
            result.append("  by (metis (mono_tags, lifting) ").append(UNIV).append("_def someI_ex subset_iff_psubset_eq");
            for (String parent : sort.extendsSorts(services).stream().map(Sort::name).map(Name::toString).toList()) {
                result.append(" ").append("bottom_in_").append(parent);
            }
            result.append(")").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("typedef ").append(sortName).append(" = \"").append(UNIV).append("\"").append(LINE_ENDING);
            String repName = sortName + "2any";
            String absName = "any2" + sortName;

            result.append("  morphisms ").append(repName).append(" ").append(absName).append(LINE_ENDING);
            result.append("  using ").append(UNIV_spec_lemma_name).append(" by auto").append(LINE_ENDING).append(LINE_ENDING);

            result.append("declare [[coercion ").append(repName).append("]]").append(LINE_ENDING).append(LINE_ENDING);

            result.append("lemma ").append(sortName).append("_type_specification[simp]:").append(getUnivSpec(services, sort, "(UNIV::" + sortName + " set)")).append(LINE_ENDING);
            result.append("  using ").append(UNIV_spec_lemma_name).append(" using type_definition.Rep_range type_definition_").append(sortName).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING).append(LINE_ENDING);

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
        result.append(LINE_ENDING);

        return result.append("end").append(LINE_ENDING).append("end");
    }

    private static String getUnivSpec(Services services, Sort sort, String insert) {
        List<String> parentSortNames = sort.extendsSorts(services).stream().map(Sort::name).map(Name::toString).toList();
        StringBuilder univSpec = new StringBuilder();
        univSpec.append("\"").append(insert).append(" \\<subseteq> (UNIV::").append(parentSortNames.get(0)).append(" set)");
        for (int i = 1; i < parentSortNames.size(); i++) {
            univSpec.append(" \\<and> ").append(insert).append(" \\<subseteq> (UNIV::").append(parentSortNames.get(i)).append(" set)");
        }
        univSpec.append(" \\<and> bottom \\<in> ").append(insert).append("\"");
        return univSpec.toString();
    }
}
