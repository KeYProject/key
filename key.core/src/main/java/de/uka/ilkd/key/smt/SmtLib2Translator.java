/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The translation for the SMT2-format. It nearly the same as for the SMT1-format.
 */
@SuppressWarnings("unused") // used via reflection by the legacy solver types
public class SmtLib2Translator extends AbstractSMTTranslator {
    // FIXME: StringBuilder::equals does not what you think it does! It is not overwritten!
    private static final StringBuilder INTSTRING = new StringBuilder("Int");

    private static final StringBuilder BOOL = new StringBuilder("Bool");

    private static final String GAP = "          ";

    private static final StringBuilder FALSESTRING = new StringBuilder("false");

    private static final StringBuilder TRUESTRING = new StringBuilder("true");

    private static final StringBuilder ALLSTRING = new StringBuilder("forall");

    private static final StringBuilder EXISTSTRING = new StringBuilder("exists");

    private static final StringBuilder ANDSTRING = new StringBuilder("and");

    private static final StringBuilder ORSTRING = new StringBuilder("or");

    private static final StringBuilder NOTSTRING = new StringBuilder("not");

    private static final StringBuilder EQSTRING = new StringBuilder("=");

    private static final StringBuilder IMPLYSTRING = new StringBuilder("=>");

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

    protected StringBuilder translateNull() {
        return NULLSTRING;
    }

    @Override
    protected StringBuilder getNullName() {
        return NULLSTRING;
    }

    protected StringBuilder translateNullSort() {
        return NULLSORTSTRING;
    }

    protected StringBuilder getBoolSort() {
        return BOOL;
    }

    /**
     * This constructor only exists to have uniform constructors for both the modular and the legacy
     * translation.
     *
     * @param handlerNames not used by this translator!
     * @param handlerOptions also not used by this translator
     * @param preamble also also not used
     */
    @SuppressWarnings("unused") // can be called via reflection
    public SmtLib2Translator(String[] handlerNames, String[] handlerOptions,
            @Nullable String preamble) {
    }

    @Override
    protected StringBuilder buildCompleteText(StringBuilder formula,
            ArrayList<StringBuilder> assumptions, ArrayList<ContextualBlock> assumptionBlocks,
            ArrayList<ArrayList<StringBuilder>> functions,
            ArrayList<ArrayList<StringBuilder>> predicates,
            ArrayList<ContextualBlock> predicateBlocks, ArrayList<StringBuilder> types,
            SortHierarchy sortHierarchy, SMTSettings settings) {
        StringBuilder result = new StringBuilder();
        /*
         * Always set logic now, (hopefully) does no harm with the modern SMT solvers we support.
         * Note that the logic to be set may be (and is) hardcoded into the SMTSettings#getLogic()
         * method (currently AUFNIRA).
         */
        // if (getConfig().mentionLogic()) {
        result.append("(set-logic ").append(settings.getLogic()).append(" )\n");
        // }
        result.append("(set-option :print-success true) \n");
        result.append("(set-option :produce-unsat-cores true)\n");
        result.append("(set-option :produce-models true)\n");
        // One cannot ask for proofs and models at one time
        // rather have models than proofs (MU, 2013-07-19)
        // see bug #1236
        // result.append("(set-option :produce-proofs true)\n");


        createSortDeclaration(types, result);
        createFunctionDeclarations(result, predicates, predicateBlocks, functions);
        StringBuilder assump = createAssumptions(assumptions, assumptionBlocks);

        result.append("(assert(not \n");
        if (assump.length() > 0) {
            result.append("(=> ").append(assump);
        }
        result.append("\n\n" + GAP + "; The formula to be proved:\n\n");

        result.append(formula);

        if (assump.length() > 0) {
            result.append("\n)" + GAP + "; End of imply.");
        }
        result.append("\n))" + GAP + "; End of assert.");
        result.append("\n\n(check-sat)");


        return result.append("\n" + GAP + "; end of smt problem declaration");
    }

    private StringBuilder createAssumptions(ArrayList<StringBuilder> assumptions,
            ArrayList<ContextualBlock> assumptionBlocks) {
        String[] commentAssumption = new String[9];
        commentAssumption[ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION] =
            "Assumptions for dummy variables:";
        commentAssumption[ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION] =
            "Assumptions for function definitions:";
        commentAssumption[ContextualBlock.ASSUMPTION_SORT_PREDICATES] =
            "Assumptions for sort predicates:";
        commentAssumption[ContextualBlock.ASSUMPTION_TYPE_HIERARCHY] =
            "Assumptions for type hierarchy:";
        commentAssumption[ContextualBlock.ASSUMPTION_TACLET_TRANSLATION] =
            "Assumptions for taclets:";
        commentAssumption[ContextualBlock.ASSUMPTION_DISTINCT] =
            "Assumptions for uniqueness of functions:";
        commentAssumption[ContextualBlock.ASSUMPTION_INTEGER] =
            "Assumptions for very small and very big integers:";
        commentAssumption[ContextualBlock.ASSUMPTION_MULTIPLICATION] =
            "Assumptions for uninterpreted multiplication:";
        commentAssumption[ContextualBlock.ASSUMPTION_SORTS_NOT_EMPTY] =
            "Assumptions for sorts - there is at least one object of every sort:";


        // add the assumptions
        ArrayList<StringBuilder> assumptionsToRemove = new ArrayList<>();
        StringBuilder assump = new StringBuilder();
        boolean needsAnd = assumptions.size() > 1;

        for (int k = 0; k < commentAssumption.length; k++) {
            ContextualBlock block = assumptionBlocks.get(k);

            if (block.getStart() <= block.getEnd()) {
                assump.append("\n" + GAP + "; ").append(commentAssumption[block.getType()])
                        .append("\n");
                for (int i = block.getStart(); i <= block.getEnd(); i++) {
                    assumptionsToRemove.add(assumptions.get(i));
                    assump.append(assumptions.get(i));
                    assump.append("\n");
                }
            }
        }


        assumptions.removeAll(assumptionsToRemove);


        if (!assumptions.isEmpty()) {
            assump.append("\n" + GAP + "; Other assumptions:\n");
            for (StringBuilder s : assumptions) {
                assump.append(s).append("\n");
            }
        }
        StringBuilder result = new StringBuilder();
        if (needsAnd) {
            result.append("(and\n");
            result.append(assump);
            result.append("\n)" + GAP + "; End of assumptions.\n");

        }
        return result;
    }

    private void createFunctionDeclarations(StringBuilder result,
            ArrayList<ArrayList<StringBuilder>> predicates,
            ArrayList<ContextualBlock> predicateBlocks,
            ArrayList<ArrayList<StringBuilder>> functions) {
        StringBuilder temp = new StringBuilder();
        createPredicateDeclaration(temp, predicates, predicateBlocks);
        createFunctionDeclaration(temp, functions);
        if (temp.length() > 0) {
            result.append(temp);
        }
    }

    private void createFunctionDeclaration(StringBuilder result,
            ArrayList<ArrayList<StringBuilder>> functions) {
        // add the function declarations
        if (!functions.isEmpty()) {
            result.append(translateComment(1, "Function declarations\n"));
            for (ArrayList<StringBuilder> function : functions) {
                createFunctionDeclaration(function, false, result);
            }
        }
    }

    private void createPredicateDeclaration(StringBuilder result,
            ArrayList<ArrayList<StringBuilder>> predicates,
            ArrayList<ContextualBlock> predicateBlocks) {
        String[] commentPredicate = new String[2];
        commentPredicate[ContextualBlock.PREDICATE_FORMULA] = "Predicates used in formula:\n";
        commentPredicate[ContextualBlock.PREDICATE_TYPE] = "Types expressed by predicates:\n";

        ArrayList<ArrayList<StringBuilder>> predicatesToRemove = new ArrayList<>();

        StringBuilder temp = new StringBuilder();

        for (int k = 0; k < commentPredicate.length; k++) {
            ContextualBlock block = predicateBlocks.get(k);


            if (block.getStart() <= block.getEnd()) {
                temp.append(translateComment(0, commentPredicate[block.getType()] + "\n"));

                for (int i = block.getStart(); i <= block.getEnd(); i++) {
                    predicatesToRemove.add(predicates.get(i));
                    createFunctionDeclaration(predicates.get(i), true, temp);
                }

            }
        }

        predicates.removeAll(predicatesToRemove);

        // add other predicates
        if (!predicates.isEmpty()) {
            temp.append(translateComment(1, "Other predicates\n"));
            for (ArrayList<StringBuilder> predicate : predicates) {
                createFunctionDeclaration(predicate, true, temp);
            }
        }

        if (temp.length() > 0) {
            result.append(temp);
        }


    }

    private void createFunctionDeclaration(ArrayList<StringBuilder> function, boolean isPredicate,
            StringBuilder result) {
        result.append("(declare-fun ");
        StringBuilder name = function.remove(0);
        StringBuilder returnType = isPredicate ? BOOL : function.remove(function.size() - 1);
        result.append(name);
        result.append(" (");
        for (StringBuilder s : function) {
            result.append(s);
            result.append(" ");
        }
        result.append(") ");
        result.append(returnType);
        result.append(" )\n");
    }

    private void createSortDeclaration(ArrayList<StringBuilder> types, StringBuilder result) {
        result.append("\n" + GAP + "; Declaration of sorts.\n");
        for (StringBuilder type : types) {
            if (!(type == INTSTRING || type.equals(INTSTRING))) {
                createSortDeclaration(type, result);
            }
        }
    }

    private void createSortDeclaration(StringBuilder type, StringBuilder result) {
        result.append("(declare-sort ").append(type).append(" 0)\n");


    }

    /**
     * Translate a sort.
     *
     * @param name the sorts name
     * @param isIntVal true, if the sort should represent some kind of integer
     * @return Argument 1 of the return value is the sort used in var declarations, Argument2 is the
     *         sort used for type predicates
     */
    protected StringBuilder translateSort(String name, boolean isIntVal) {
        return makeUnique(new StringBuilder(name));
    }

    @Override
    protected boolean isMultiSorted() {
        return true;
    }

    @Override
    protected StringBuilder getIntegerSort() {
        return INTSTRING;
    }

    @Override
    protected StringBuilder translateFunction(StringBuilder name, ArrayList<StringBuilder> args) {
        return buildFunction(name, args);
    }

    @Override
    protected StringBuilder translateFunctionName(StringBuilder name) {
        return makeUnique(name);
    }

    @Override
    protected StringBuilder translateIntegerDiv(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(DIVSTRING, args);
    }


    @Override
    protected StringBuilder translateIntegerGeq(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(GEQSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerGt(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(GTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerLeq(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(LEQSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerLt(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(LTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerMinus(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerMod(StringBuilder arg1, StringBuilder arg2) {
        return new StringBuilder("unknownOp");
    }

    @Override
    protected StringBuilder translateIntegerMult(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(MULTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerPlus(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(PLUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerUnaryMinus(StringBuilder arg) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        StringBuilder n = new StringBuilder("0");
        args.add(n);
        args.add(arg);
        return buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerValue(long val) {

        StringBuilder arg = new StringBuilder(Long.toString(val));

        if (val < 0) {
            // delete the minus sign.
            arg = new StringBuilder(arg.substring(1, arg.length()));
            arg = translateIntegerUnaryMinus(arg);
        }

        return arg;
    }

    @Override
    protected StringBuilder translateLogicalConstant(StringBuilder name) {
        return makeUnique(name);
    }

    @Override
    protected StringBuilder translateLogicalVar(StringBuilder name) {
        return (new StringBuilder()).append(makeUnique(name));
    }

    @Override
    protected StringBuilder translateLogicalAll(StringBuilder var, StringBuilder type,
            StringBuilder form) {
        StringBuilder toReturn = new StringBuilder();
        toReturn.append("(");
        toReturn.append(ALLSTRING);

        toReturn.append(" ((");
        toReturn.append(var);
        toReturn.append(" ");
        toReturn.append(type);
        toReturn.append(")) ");

        toReturn.append(form);

        toReturn.append(")");
        return toReturn;
    }

    @Override
    protected StringBuilder translateLogicalAnd(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(ANDSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalEquivalence(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);

        ArrayList<StringBuilder> argsrev = new ArrayList<>();
        argsrev.add(arg2);
        argsrev.add(arg1);

        ArrayList<StringBuilder> forms = new ArrayList<>();
        forms.add(buildFunction(IMPLYSTRING, args));
        forms.add(buildFunction(IMPLYSTRING, argsrev));
        return buildFunction(ANDSTRING, forms);
    }

    @Override
    protected StringBuilder translateLogicalExist(StringBuilder var, StringBuilder type,
            StringBuilder form) {
        StringBuilder toReturn = new StringBuilder();
        toReturn.append("(");
        toReturn.append(EXISTSTRING);

        toReturn.append("((");
        toReturn.append(var);
        toReturn.append(" ");
        toReturn.append(type);
        toReturn.append("))");

        toReturn.append(form);

        toReturn.append(")");
        return toReturn;
    }

    @Override
    protected StringBuilder translateLogicalFalse() {
        return new StringBuilder(FALSESTRING);
    }

    @Override
    protected StringBuilder translateLogicalImply(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(IMPLYSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalNot(StringBuilder arg) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg);
        return buildFunction(NOTSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalOr(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(ORSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalTrue() {
        return new StringBuilder(TRUESTRING);
    }

    @Override
    protected StringBuilder translateObjectEqual(StringBuilder arg1, StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(EQSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalIfThenElse(StringBuilder cond, StringBuilder ifterm,
            StringBuilder elseterm) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(cond);
        args.add(ifterm);
        args.add(elseterm);
        return buildFunction(LOGICALIFTHENELSE, args);
    }

    @Override
    protected StringBuilder translateTermIfThenElse(StringBuilder cond, StringBuilder ifterm,
            StringBuilder elseterm) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(cond);
        args.add(ifterm);
        args.add(elseterm);
        return buildFunction(TERMIFTHENELSE, args);
    }

    @Override
    protected StringBuilder translatePredicate(StringBuilder name, ArrayList<StringBuilder> args) {

        return buildFunction(name, args);
    }

    @Override
    protected StringBuilder translatePredicateName(StringBuilder name) {
        return makeUnique(name);
    }


    @Override
    protected StringBuilder translateDistinct(FunctionWrapper[] fw, Services services) {
        if (getSettings() == null || !getSettings().useBuiltInUniqueness()) {
            return super.translateDistinct(fw, services);
        }
        int start = 0;
        ArrayList<ArrayList<StringBuilder>> temp = new ArrayList<>();

        StringBuilder rightSide = new StringBuilder();
        rightSide.append("( ").append(DISTINCT).append(" ");
        for (int i = 0; i < fw.length; i++) {
            temp.add(createGenericVariables(fw[i].getFunction().arity(), start));
            start += fw[i].getFunction().arity();
            rightSide.append(buildFunction(fw[i].getName(), temp.get(i))).append(" ");

        }

        rightSide.append(")");

        for (int j = 0; j < fw.length; j++) {
            for (int i = 0; i < fw[j].getFunction().arity(); i++) {
                Sort sort = fw[j].getFunction().argSorts().get(i);
                rightSide =
                    translateLogicalAll(temp.get(j).get(i), usedDisplaySort.get(sort), rightSide);

            }
        }
        return rightSide;

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


    @Override
    protected StringBuilder translateComment(int newLines, String comment) {
        StringBuilder buffer = new StringBuilder();
        buffer.append("\n".repeat(Math.max(0, newLines)));
        return buffer.append(GAP + "; ").append(comment);
    }


}
