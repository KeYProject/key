package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableArray;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProblem.sequentToTerm;

public class IsabelleTranslator {

    private final HashMap<Sort, StringBuilder> usedSorts = new HashMap<>();

    private final HashMap<Function, StringBuilder> usedFunctions = new HashMap<>();

    private final HashMap<Function, StringBuilder> usedPredicates = new HashMap<>();

    private static final StringBuilder INTSTRING = new StringBuilder("Int");

    private static final StringBuilder BOOL = new StringBuilder("bool");

    private static final String GAP = "          ";

    private static final StringBuilder FALSESTRING = new StringBuilder("False");

    private static final StringBuilder TRUESTRING = new StringBuilder("True");

    private static final StringBuilder ALLSTRING = new StringBuilder("\\<forall>");

    private static final StringBuilder EXISTSTRING = new StringBuilder("\\<exists>");

    private static final StringBuilder ANDSTRING = new StringBuilder("\\<and>");

    private static final StringBuilder ORSTRING = new StringBuilder("\\<or>");

    private static final StringBuilder NOTSTRING = new StringBuilder("\\<not>");

    private static final StringBuilder EQSTRING = new StringBuilder("=");

    private static final StringBuilder IMPLYSTRING = new StringBuilder("-->");

    private static final StringBuilder PLUSSTRING = new StringBuilder("+");

    private static final StringBuilder MINUSSTRING = new StringBuilder("-");

    private static final StringBuilder MULTSTRING = new StringBuilder("*");

    private static final StringBuilder DIVSTRING = new StringBuilder("div");

    private static final StringBuilder LTSTRING = new StringBuilder("<");

    private static final StringBuilder GTSTRING = new StringBuilder(">");

    private static final StringBuilder LEQSTRING = new StringBuilder("<=");

    private static final StringBuilder GEQSTRING = new StringBuilder(">=");

    private static final StringBuilder NULLSTRING = new StringBuilder("null");

    private static final StringBuilder NULLSORTSTRING = new StringBuilder("NULLSORT");

    private static final StringBuilder LOGICALIFTHENELSE = new StringBuilder("ite");

    private static final StringBuilder TERMIFTHENELSE = new StringBuilder("ite");

    private static final StringBuilder DISTINCT = new StringBuilder("distinct");

    public final StringBuilder translateProblem(Sequent sequent, Services services) throws IllegalFormulaException {
        Term problem = sequentToTerm(sequent, services);
        // TODO find correct values
        StringBuilder hb = buildCompleteText(translateTerm(problem, new ArrayList<>(), services), new ArrayList<>());
        return hb;
    }

    protected StringBuilder buildCompleteText(StringBuilder formula, ArrayList<StringBuilder> types) {
        //TODO ensure usedSorts etc have the right values?
        StringBuilder result = new StringBuilder();
        result.append("theory Translation imports Main begin").append(System.lineSeparator());

        result.append(getSortDeclarations());

        result.append("locale varsAndFunctions =").append(System.lineSeparator());
        //TODO additional types of JFOL hierarchy and assumptions
        result.append(getNullLocale());

        result.append(getFunctionDeclarations());
        result.append(getPredicateDeclarations());
        result.append(getFreeVariableDeclarations());

        result.append("begin").append(System.lineSeparator());

        result.append("theorem solve: \"");
        result.append(formula).append("\"");
        result.append(System.lineSeparator());

        return result.append("end").append(System.lineSeparator()).append("end");
    }

    private StringBuilder getNullLocale() {
        //TODO handle null correctly. Probably null != undefined (Isabelle)
        StringBuilder result = new StringBuilder();
        result.append("fixes null::'a").append(System.lineSeparator());
        result.append("assumes null_undef: \"null = undefined\"").append(System.lineSeparator());
        return result;
    }

    private StringBuilder getFunctionDeclarations() {
        StringBuilder declarations = new StringBuilder();
        for (Function fun : usedFunctions.keySet()) {
            declarations.append(getFunctionDeclaration(fun)).append(System.lineSeparator());
        }
        return declarations;
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

    private StringBuilder getPredicateDeclarations() {
        StringBuilder declarations = new StringBuilder();
        for (Function fun : usedPredicates.keySet()) {
            declarations.append(getPredicateDeclaration(fun)).append(System.lineSeparator());
        }
        return declarations;
    }

    private StringBuilder getPredicateDeclaration(Function fun) {
        //TODO duplicate handling? Isabelle function handling?
        StringBuilder result = new StringBuilder();
        result.append("fixes ");
        result.append(usedPredicates.get(fun));
        result.append(":: \"");
        for (Sort sort : fun.argSorts()) {
            result.append(translateSort(sort)).append("=>");
        }
        result.append(BOOL).append("\"");
        return result;
    }

    private StringBuilder getFreeVariableDeclarations() {
        //TODO implement
        return new StringBuilder();
    }


    private StringBuilder getSortDeclarations() {
        StringBuilder declaration = new StringBuilder();
        for (Sort sort : usedSorts.keySet()) {
            declaration.append(getSortDeclaration(sort));
        }
        return declaration;
    }

    private StringBuilder getSortDeclaration(Sort sort) {
        StringBuilder result = new StringBuilder();
        return result.append("typedecl ").append(usedSorts.get(sort)).append(System.lineSeparator());
    }

    private StringBuilder translateTerm(Term term, List<QuantifiableVariable> quantifiedVariables, Services services) {
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
        return new StringBuilder();
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
            toReturn.append("(");
            toReturn.append(name).append(" ");

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

    protected StringBuilder translateComment(int newLines, String comment) {
        StringBuilder buffer = new StringBuilder();
        buffer.append("\n".repeat(Math.max(0, newLines)));
        return buffer.append(GAP + "; ").append(comment);
    }
}
