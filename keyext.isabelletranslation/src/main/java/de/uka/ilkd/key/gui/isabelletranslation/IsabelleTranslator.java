package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableArray;

import java.io.IOException;
import java.util.ArrayList;
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

            result.append("lemma ex_").append(UNIV).append(":");
            result.append(getUnivSpec(services, sort, "{bottom}")).append(LINE_ENDING);
            result.append("  by simp").append(LINE_ENDING).append(LINE_ENDING);


            result.append("consts").append(LINE_ENDING).append(UNIV).append("::\"any set\"").append(LINE_ENDING);
            result.append(LINE_ENDING);

            result.append("specification (").append(UNIV).append(") ");
            result.append(getUnivSpec(services, sort, UNIV)).append(LINE_ENDING);
            result.append("  using ex_").append(UNIV).append(" by blast").append(LINE_ENDING);
            result.append(LINE_ENDING);

            String UNIV_spec_lemma_name = UNIV + "_specification";
            result.append("lemma ").append(UNIV_spec_lemma_name).append(":").append(getUnivSpec(services, sort, UNIV)).append(LINE_ENDING);
            result.append("  by (metis (mono_tags, lifting) ").append(UNIV).append("_def UNIV_I subset_UNIV verit_sko_ex_indirect)").append(LINE_ENDING);
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

    private StringBuilder getNullLocale() {
        //TODO handle null correctly
        StringBuilder result = new StringBuilder();
        result.append("fixes null::'a").append(LINE_ENDING);
        return result;
    }


    private StringBuilder getFunctionDeclaration(Function fun) {
        //TODO duplicate handling? Isabelle function handling?
        StringBuilder result = new StringBuilder();
        result.append("fixes ");
        result.append(usedFunctions.get(fun));
        result.append(":: \"");
        for (Sort sort : fun.argSorts()) {
            result.append(translateSort(sort)).append("=>");
        }
        result.append(translateSort(fun.sort())).append("\"");
        return result;
    }

    private StringBuilder translateTerm(Term term, List<QuantifiableVariable> quantifiedVariables, Services services) throws IllegalFormulaException {
        Operator op = term.op();

        if (op == Junctor.IMP) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVariables, services);
            return translateImplication(arg1, arg2);
        } else if (op == Junctor.AND) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVariables, services);
            return translateAnd(arg1, arg2);
        } else if (op == Junctor.OR) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVariables, services);
            return translateLogicalOr(arg1, arg2);
        } else if (op == Junctor.NOT) {
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            return translateNot(arg1);
        } else if (op == Junctor.TRUE) {
            return translateLogicalTrue();
        } else if (op == Junctor.FALSE) {
            return translateLogicalFalse();
        } else if (op == Equality.EQUALS) {
            //TODO type hierarchy and cast handling
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            StringBuilder arg2 = translateTerm(term.sub(1), quantifiedVariables, services);
            return translateObjectEqual(arg1, arg2);
        } else if (op instanceof Function fun) {
            ArrayList<StringBuilder> args = new ArrayList<>();
            for (int i = 0; i < op.arity(); i++) {
                args.add(translateTerm(term.sub(i), quantifiedVariables, services));
            }
            if (fun.sort() == Sort.FORMULA) {
                return translatePredicate(fun, args);
            }
            //TODO binding functions???
            return translateFunction(fun, args);
        } else if ((op instanceof LogicVariable) || (op instanceof ProgramVariable)) {
            //TODO handle Logic and Program variables differently?
            //TODO quantified variables handling
            ParsableVariable var = (ParsableVariable) op;
            if (quantifiedVariables.contains(op)) {
                return translateVariable(var);
            } else {
                return translateVariable(var);
            }
        } else if (op == Quantifier.ALL) {
            ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
            Debug.assertTrue(vars.size() == 1);

            QuantifiableVariable var = vars.get(0);

            quantifiedVariables.add(var);

            StringBuilder qv = this.translateVariable(var);
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            return this.translateLogicalAll(qv, arg1);
        } else if (op == Quantifier.EX) {
            ImmutableArray<QuantifiableVariable> vars = term.varsBoundHere(0);
            Debug.assertTrue(vars.size() == 1);

            QuantifiableVariable var = vars.get(0);

            quantifiedVariables.add(var);

            StringBuilder qv = this.translateVariable(var);
            StringBuilder arg1 = translateTerm(term.sub(0), quantifiedVariables, services);
            return this.translateLogicalExists(qv, arg1);
        }
        //TODO translation of other types
        throw new IllegalFormulaException("");
    }

    private StringBuilder translateLogicalFalse() {
        return FALSESTRING;
    }

    private StringBuilder translateLogicalTrue() {
        return TRUESTRING;
    }

    private StringBuilder translateObjectEqual(StringBuilder arg1, StringBuilder arg2) {
        StringBuilder result = new StringBuilder();
        return surroundBrackets(result.append(arg1).append(EQSTRING).append(arg2));
    }

    private StringBuilder translateLogicalOr(StringBuilder arg1, StringBuilder arg2) {
        StringBuilder toReturn = new StringBuilder();
        return surroundBrackets(toReturn.append(arg1).append(ORSTRING).append(arg2));
    }

    private StringBuilder translateLogicalExists(StringBuilder qv, StringBuilder arg1) {
        StringBuilder result = new StringBuilder();
        result.append(EXISTSTRING);
        result.append(qv).append(". ");
        result.append(arg1);
        return surroundBrackets(result);
    }

    private StringBuilder translateSort(Sort sort) {
        StringBuilder result = new StringBuilder();
        if (usedSorts.containsKey(sort)) {
            return usedSorts.get(sort);
        }
        //TODO prevent unintentional translation into Isabelle types
        //TODO prevent duplicates?
        usedSorts.put(sort, new StringBuilder(sort.name().toString()));
        return result.append(sort.name().toString());
    }

    private StringBuilder translateLogicalAll(StringBuilder qv, StringBuilder arg1) {
        StringBuilder result = new StringBuilder();
        result.append(ALLSTRING);
        result.append(qv).append(". ");
        result.append(arg1);
        return surroundBrackets(result);
    }

    private StringBuilder translatePredicate(Function fun, ArrayList<StringBuilder> args) {
        if (!usedPredicates.containsKey(fun)) {
            //TODO avoid conflicts
            StringBuilder funName = new StringBuilder(fun.name().toString());
            usedPredicates.put(fun, funName);
        }
        return buildFunction(usedPredicates.get(fun), args);
    }

    private StringBuilder buildFunction(StringBuilder name, ArrayList<StringBuilder> args) {
        StringBuilder toReturn = new StringBuilder();
        if (args.isEmpty()) {
            toReturn.append(name);
        } else {
            toReturn.append("((");
            toReturn.append(name).append(") ");

            for (StringBuilder arg : args) {
                toReturn.append(arg).append(" ");
            }
            toReturn.append(")");
        }
        return toReturn;
    }

    private StringBuilder surroundBrackets(StringBuilder sb) {
        return new StringBuilder("(").append(sb).append(")");
    }

    private StringBuilder translateAnd(StringBuilder arg1, StringBuilder arg2) {
        StringBuilder toReturn = new StringBuilder();
        return surroundBrackets(toReturn.append(arg1).append(ANDSTRING).append(arg2));
    }

    private StringBuilder translateFunction(Function fun, ArrayList<StringBuilder> args) {
        if (!usedFunctions.containsKey(fun)) {
            //TODO avoid conflicts
            StringBuilder funName = new StringBuilder(fun.name().toString());
            usedFunctions.put(fun, funName);
        }
        return buildFunction(usedFunctions.get(fun), args);
    }

    private StringBuilder translateVariable(ParsableVariable var) {
        //TODO Prevent Duplicates?
        StringBuilder result = new StringBuilder();
        return surroundBrackets(result.append(var.name().toString()).append("::").append(translateSort(var.sort())));
    }

    private StringBuilder translateNot(StringBuilder arg1) {
        StringBuilder toReturn = new StringBuilder();
        return surroundBrackets(toReturn.append(NOTSTRING).append(arg1));
    }

    private StringBuilder translateImplication(StringBuilder arg1, StringBuilder arg2) {
        StringBuilder toReturn = new StringBuilder();
        return surroundBrackets(toReturn.append(arg1).append(IMPLYSTRING).append(arg2));
    }
}
