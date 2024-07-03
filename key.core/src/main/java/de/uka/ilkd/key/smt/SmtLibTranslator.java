/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.smt;

import java.util.ArrayList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.sort.Sort;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SmtLibTranslator extends AbstractSMTTranslator {
    private static final Logger LOGGER = LoggerFactory.getLogger(SmtLibTranslator.class);

    private static final StringBuilder INTSTRING = new StringBuilder("Int");

    private static final StringBuilder BOOL = new StringBuilder("Bool");

    private static final StringBuilder FALSESTRING = new StringBuilder("false");

    private static final StringBuilder TRUESTRING = new StringBuilder("true");

    private static final StringBuilder ALLSTRING = new StringBuilder("forall");

    private static final StringBuilder EXISTSTRING = new StringBuilder("exists");

    private static final StringBuilder ANDSTRING = new StringBuilder("and");

    private static final StringBuilder ORSTRING = new StringBuilder("or");

    private static final StringBuilder NOTSTRING = new StringBuilder("not");

    private static final StringBuilder EQSTRING = new StringBuilder("=");

    private static final StringBuilder IMPLYSTRING = new StringBuilder("implies");

    private static final StringBuilder PLUSSTRING = new StringBuilder("+");

    private static final StringBuilder MINUSSTRING = new StringBuilder("-");

    private static final StringBuilder MULTSTRING = new StringBuilder("*");

    private static final StringBuilder LTSTRING = new StringBuilder("<");

    private static final StringBuilder GTSTRING = new StringBuilder(">");

    private static final StringBuilder LEQSTRING = new StringBuilder("<=");

    private static final StringBuilder GEQSTRING = new StringBuilder(">=");

    private static final StringBuilder NULLSTRING = new StringBuilder("null");

    private static final StringBuilder NULLSORTSTRING = new StringBuilder("NULLSORT");

    private static final StringBuilder LOGICALIFTHENELSE = new StringBuilder("if_then_else");

    private static final StringBuilder TERMIFTHENELSE = new StringBuilder("ite");

    private static final StringBuilder DISTINCT = new StringBuilder("distinct");

    /**
     * Just a constructor which starts the conversion to Simplify syntax.
     * The result can be fetched with
     *
     * @param sequent The sequent which shall be translated.
     * @param services The Services Object belonging to the sequent.
     */
    public SmtLibTranslator(Sequent sequent, Services services, Configuration config) {
        super(sequent, services, config);
    }

    /**
     * For translating only terms and not complete sequents.
     */
    public SmtLibTranslator(Services s, Configuration config) {
        super(s, config);
    }

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

    @Override
    protected StringBuilder buildCompleteText(StringBuilder formula,
            ArrayList<StringBuilder> assumptions,
            ArrayList<ContextualBlock> assumptionBlocks,
            ArrayList<ArrayList<StringBuilder>> functions,
            ArrayList<ArrayList<StringBuilder>> predicates,
            ArrayList<ContextualBlock> predicateBlocks,
            ArrayList<StringBuilder> types, SortHierarchy sortHierarchy,
            SMTSettings settings) {

        StringBuilder toReturn = new StringBuilder(
            "( benchmark KeY_translation\n");
        // add the sortdeclarations
        // as sortshierarchies are not supported by smt-lib, only one
        // sort should be used
        // no extra sorts needed

        String[] commentPredicate = new String[2];
        commentPredicate[ContextualBlock.PREDICATE_FORMULA] =
            "\n\n:notes \"Predicates used in formula:\"";
        commentPredicate[ContextualBlock.PREDICATE_TYPE] =
            "\n\n:notes \"Types expressed by predicates:\"";
        String[] commentAssumption = new String[9];
        commentAssumption[ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION] =
            "\n\n:notes \"Assumptions for dummy variables:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION] =
            "\n\n:notes \"Assumptions for function definitions:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_SORT_PREDICATES] =
            "\n\n:notes \"Assumptions for sort predicates:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_TYPE_HIERARCHY] =
            "\n\n:notes \"Assumptions for type hierarchy:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_TACLET_TRANSLATION] =
            "\n\n:notes \"Assumptions for taclets:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_DISTINCT] =
            "\n\n:notes \"Assumptions for uniqueness of functions:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_INTEGER] =
            "\n\n:notes \"Assumptions for very small and very big integers:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_MULTIPLICATION] =
            "\n\n:notes \"Assumptions for uninterpreted multiplication:\"";
        commentAssumption[ContextualBlock.ASSUMPTION_SORTS_NOT_EMPTY] =
            "\n\n:notes \"Assumptions for sorts - there is at least one object of every sort:\"";


        // add the logic definition
        toReturn.append("\n:logic AUFLIA");

        // add the sort declarations
        StringBuilder extrasorts = new StringBuilder();
        for (StringBuilder s : types) {
            if (!(s == INTSTRING || s.equals(INTSTRING))) {
                extrasorts.append(s);
                extrasorts.append(" ");
            }
        }
        if (extrasorts.length() > 0) {
            toReturn.append("\n :extrasorts (");
            toReturn.append(extrasorts);
            toReturn.append(")");
        }

        // add the predicate declarations
        // add the predicate declarations for formula predicates
        ArrayList<ArrayList<StringBuilder>> predicatesToRemove = new ArrayList<>();

        StringBuilder preds = new StringBuilder();

        for (int k = 0; k < commentPredicate.length; k++) {
            ContextualBlock block = predicateBlocks.get(k);


            if (block.getStart() <= block.getEnd()) {
                preds.append(commentPredicate[block.getType()]);
                preds.append("\n:extrapreds (");
                for (int i = block.getStart(); i <= block.getEnd(); i++) {
                    preds.append("(");
                    predicatesToRemove.add(predicates.get(i));
                    for (StringBuilder s : predicates.get(i)) {
                        preds.append(s);
                        preds.append(" ");
                    }
                    preds.append(") ");
                }
                preds.append(")");
            }
        }


        predicates.removeAll(predicatesToRemove);

        // add other predicates
        if (!predicates.isEmpty()) {
            preds = preds.append("\n\n:notes \"Other predicates\"");
            preds.append("\n:extrapreds (");
            for (ArrayList<StringBuilder> a : predicates) {
                preds.append("(");
                for (StringBuilder s : a) {
                    preds.append(s);
                    preds.append(" ");
                }
                preds.append(") ");
            }
            preds.append(")");
        }

        toReturn.append(preds);

        // add the function declarations
        if (!functions.isEmpty()) {
            toReturn.append("\n\n:notes \"Function declarations\"");
            toReturn.append("\n:extrafuns (");
            for (ArrayList<StringBuilder> a : functions) {
                toReturn.append("(");
                for (StringBuilder s : a) {
                    toReturn.append(s);
                    toReturn.append(" ");
                }
                toReturn.append(") ");
            }
            toReturn.append(")");
        }

        // add the assumptions
        ArrayList<StringBuilder> assumptionsToRemove = new ArrayList<>();
        StringBuilder assump = new StringBuilder();

        for (int k = 0; k < commentAssumption.length; k++) {
            ContextualBlock block = assumptionBlocks.get(k);

            if (block.getStart() <= block.getEnd()) {
                assump.append(commentAssumption[block.getType()]);
                for (int i = block.getStart(); i <= block.getEnd(); i++) {
                    assumptionsToRemove.add(assumptions.get(i));
                    assump.append("\n:assumption ").append(assumptions.get(i));
                }
            }
        }


        assumptions.removeAll(assumptionsToRemove);


        if (!assumptions.isEmpty()) {
            assump.append("\n\n:notes \"Other assumptions:\"");
            for (StringBuilder s : assumptions) {
                assump.append("\n:assumption ").append(s);
            }
        }

        toReturn.append(assump);

        // add the formula
        toReturn.append("\n\n:notes \"The formula to be proved:\"");
        formula = this.translateLogicalNot(formula);
        toReturn.append("\n:formula ").append(formula).append("\n");

        toReturn.append(")");
        LOGGER.info("Resulting formula after translation: {}", toReturn);
        return toReturn;

    }

    /**
     * Translate a sort.
     *
     * @param name the sorts name
     * @param isIntVal true, if the sort should represent some kind of
     *        integer
     * @return Argument 1 of the return value is the sort used in var
     *         declarations, Argument2 is the sort used for type predicates
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
    protected StringBuilder translateFunction(StringBuilder name,
            ArrayList<StringBuilder> args) {
        return buildFunction(name, args);
    }

    @Override
    protected StringBuilder translateFunctionName(StringBuilder name) {
        return makeUnique(name);
    }

    @Override
    protected StringBuilder translateIntegerDiv(StringBuilder arg1,
            StringBuilder arg2) {
        return new StringBuilder("unknownOp");
    }

    @Override
    protected StringBuilder translateIntegerGeq(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(GEQSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerGt(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(GTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerLeq(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(LEQSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerLt(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(LTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerMinus(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerMod(StringBuilder arg1,
            StringBuilder arg2) {
        return new StringBuilder("unknownOp");
    }

    @Override
    protected StringBuilder translateIntegerMult(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(MULTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerPlus(StringBuilder arg1,
            StringBuilder arg2) {
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
        return (new StringBuilder("?")).append(makeUnique(name));
    }

    @Override
    protected StringBuilder translateLogicalAll(StringBuilder var,
            StringBuilder type, StringBuilder form) {
        StringBuilder toReturn = new StringBuilder();
        toReturn.append("(");
        toReturn.append(ALLSTRING);

        toReturn.append(" (");
        toReturn.append(var);
        toReturn.append(" ");
        toReturn.append(type);
        toReturn.append(") ");

        toReturn.append(form);

        toReturn.append(")");
        return toReturn;
    }

    @Override
    protected StringBuilder translateLogicalAnd(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(arg1);
        args.add(arg2);
        return buildFunction(ANDSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalEquivalence(StringBuilder arg1,
            StringBuilder arg2) {
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
    protected StringBuilder translateLogicalExist(StringBuilder var,
            StringBuilder type, StringBuilder form) {
        StringBuilder toReturn = new StringBuilder();
        toReturn.append("(");
        toReturn.append(EXISTSTRING);

        toReturn.append("(");
        toReturn.append(var);
        toReturn.append(" ");
        toReturn.append(type);
        toReturn.append(")");

        toReturn.append(form);

        toReturn.append(")");
        return toReturn;
    }

    @Override
    protected StringBuilder translateLogicalFalse() {
        return new StringBuilder(FALSESTRING);
    }

    @Override
    protected StringBuilder translateLogicalImply(StringBuilder arg1,
            StringBuilder arg2) {
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
    protected StringBuilder translateLogicalOr(StringBuilder arg1,
            StringBuilder arg2) {
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
    protected StringBuilder translateObjectEqual(StringBuilder arg1,
            StringBuilder arg2) {
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
            StringBuilder elseterm) throws IllegalFormulaException {
        ArrayList<StringBuilder> args = new ArrayList<>();
        args.add(cond);
        args.add(ifterm);
        args.add(elseterm);
        return buildFunction(TERMIFTHENELSE, args);
    }

    @Override
    protected StringBuilder translatePredicate(StringBuilder name,
            ArrayList<StringBuilder> args) {
        return buildFunction(name, args);
    }

    @Override
    protected StringBuilder translatePredicateName(StringBuilder name) {
        return makeUnique(name);
    }


    @Override
    protected StringBuilder translateDistinct(FunctionWrapper[] fw) {
        if (getSettings() == null || !getSettings().useBuiltInUniqueness()) {
            return super.translateDistinct(fw);
        }
        int start = 0;
        ArrayList<ArrayList<StringBuilder>> temp = new ArrayList<>();

        StringBuilder rightSide = new StringBuilder();
        rightSide.append("( " + DISTINCT + " ");
        for (int i = 0; i < fw.length; i++) {
            temp.add(createGenericVariables(fw[i].getFunction().arity(), start));
            start += fw[i].getFunction().arity();
            rightSide.append(buildFunction(fw[i].getName(), temp.get(i)) + " ");

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

    private StringBuilder buildFunction(StringBuilder name,
            ArrayList<StringBuilder> args) {
        StringBuilder toReturn = new StringBuilder();
        if (args.size() == 0) {
            toReturn.append(name);
        } else {
            toReturn.append("(");
            toReturn.append(name);
            for (int i = 0; i < args.size(); i++) {
                toReturn.append(" ");
                toReturn.append(args.get(i));
            }
            toReturn.append(")");
        }
        return toReturn;
    }


}
