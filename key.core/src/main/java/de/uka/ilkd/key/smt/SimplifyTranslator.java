/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.smt;

import java.util.ArrayList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;


public class SimplifyTranslator extends AbstractSMTTranslator {


    private static final StringBuilder INTSTRING = new StringBuilder("int");

    private static final StringBuilder BOOLSTRING = new StringBuilder("bool");

    private static final StringBuilder FALSESTRING = new StringBuilder("FALSE");

    private static final StringBuilder TRUESTRING = new StringBuilder("TRUE");

    private static final StringBuilder ALLSTRING = new StringBuilder("FORALL");

    private static final StringBuilder EXISTSTRING = new StringBuilder("EXISTS");

    private static final StringBuilder ANDSTRING = new StringBuilder("AND");

    private static final StringBuilder ORSTRING = new StringBuilder("OR");

    private static final StringBuilder NOTSTRING = new StringBuilder("NOT");

    private static final StringBuilder EQSTRING = new StringBuilder("EQ");

    private static final StringBuilder IMPLYSTRING = new StringBuilder("IMPLIES");

    private static final StringBuilder PLUSSTRING = new StringBuilder("+");

    private static final StringBuilder MINUSSTRING = new StringBuilder("-");

    private static final StringBuilder MULTSTRING = new StringBuilder("*");

    private static final StringBuilder LTSTRING = new StringBuilder("<");

    private static final StringBuilder GTSTRING = new StringBuilder(">");

    private static final StringBuilder LEQSTRING = new StringBuilder("<=");

    private static final StringBuilder GEQSTRING = new StringBuilder(">=");

    private static final StringBuilder NULLSTRING = new StringBuilder("null");

    private static final StringBuilder NULLSORTSTRING = new StringBuilder("NULLSORT");


    /**
     * Just a constructor which starts the conversion to Simplify syntax.
     * The result can be fetched with
     *
     * @param sequent
     *        The sequent which shall be translated.
     *
     * @param services
     *        The services Object belonging to the sequent.
     */
    public SimplifyTranslator(Sequent sequent, Services services, Configuration config) {
        super(sequent, services, config);
    }

    public SimplifyTranslator(Services services, Configuration config) {
        super(services, config);
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

        StringBuilder toReturn = new StringBuilder();

        String[] commentPredicate = new String[2];
        commentPredicate[ContextualBlock.PREDICATE_FORMULA] = "\n;Predicates used in formula:\n";
        commentPredicate[ContextualBlock.PREDICATE_TYPE] = "\n;Types expressed by predicates:\n";
        String[] commentAssumption = new String[9];
        commentAssumption[ContextualBlock.ASSUMPTION_DUMMY_IMPLEMENTATION] =
            "\n\n;Assumptions for dummy variables:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_FUNCTION_DEFINTION] =
            "\n\n;Assumptions for function definitions:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_SORT_PREDICATES] =
            "\n\n;Assumptions for sort predicates:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_TYPE_HIERARCHY] =
            "\n\n;Assumptions for type hierarchy:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_TACLET_TRANSLATION] =
            "\n\n;Assumptions for taclets:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_DISTINCT] =
            "\n\n;Assumptions for uniqueness of functions:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_INTEGER] =
            "\n\n;Assumptions for very small and very big integers:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_MULTIPLICATION] =
            "\n\n;Assumptions for uninterpreted multiplication:\n";
        commentAssumption[ContextualBlock.ASSUMPTION_SORTS_NOT_EMPTY] =
            "\n\n;Assumptions for sorts - there is at least one object of every sort.:\n";



        StringBuilder comment = new StringBuilder("\n\n;The formula:\n");
        formula = comment.append(formula);

        ArrayList<ArrayList<StringBuilder>> PredicatesToRemove =
            new ArrayList<ArrayList<StringBuilder>>();

        StringBuilder preds = new StringBuilder();

        for (int k = 0; k < commentPredicate.length; k++) {
            ContextualBlock block = predicateBlocks.get(k);

            if (block.getStart() <= block.getEnd()) {
                preds.append(commentPredicate[block.getType()]);
                for (int j = block.getStart(); j <= block.getEnd(); j++) {
                    PredicatesToRemove.add(predicates.get(j));
                    preds.append("(DEFPRED (" + predicates.get(j).get(0));
                    for (int i = 1; i < predicates.get(j).size(); i++) {
                        StringBuilder var = new StringBuilder("x");
                        var = this.makeUnique(var);
                        preds.append(" " + var);
                    }
                    preds.append("))\n");
                }
            }
        }


        predicates.removeAll(PredicatesToRemove);
        if (predicates.size() > 0) {
            preds.append("\n;Other predicates:\n");
            for (ArrayList<StringBuilder> s : predicates) {
                preds.append("(DEFPRED (" + s.get(0));
                for (int i = 1; i < s.size(); i++) {
                    StringBuilder var = new StringBuilder("x");
                    var = this.makeUnique(var);
                    preds.append(" " + var);
                }
                preds.append("))\n");
            }
        }

        toReturn.append(preds);
        toReturn.append("\n");

        ArrayList<StringBuilder> AssumptionsToRemove = new ArrayList<StringBuilder>();
        StringBuilder assump = new StringBuilder();

        if (assumptions.size() > 0) {
            for (int k = 0; k < commentAssumption.length; k++) {
                ContextualBlock block = assumptionBlocks.get(k);

                if (block.getStart() <= block.getEnd()) {

                    // necessary for appending 'ANDs' correctly
                    // Without if-clause the left side of the first logical and could be empty
                    StringBuilder temp = new StringBuilder();
                    int start = block.getStart();
                    if (assump.length() == 0) {
                        temp.append(assumptions.get(start));
                        AssumptionsToRemove.add(assumptions.get(start));
                        start++;
                    }
                    assump.append(commentAssumption[block.getType()]);
                    assump.append(temp);

                    for (int i = start; i <= block.getEnd(); i++) {
                        assump = this.translateLogicalAnd(assump, assumptions.get(i));
                        AssumptionsToRemove.add(assumptions.get(i));
                    }

                }


            }

            assumptions.removeAll(AssumptionsToRemove);

            if (assumptions.size() > 0) {
                int start = 0;
                StringBuilder temp = new StringBuilder(); // TODO: temp is never used
                if (assump.length() == 0) {
                    temp.append(assumptions.get(start));
                    start++;
                }
                assump.append("\n\n;Other assumptions:\n");

                for (int i = start; i < assumptions.size(); i++) {
                    assump = this.translateLogicalAnd(assump, assumptions.get(i));
                }

            }


            formula = this.translateLogicalImply(assump, formula);
            formula.append("\n");
        }



        /*
         * CAUTION!! For some reason, the solver gives the correct result,
         * if this part is added. The reason, why this is, is not clear to me yet!
         */
        StringBuilder temp = new StringBuilder();
        temp.append("(").append(ALLSTRING).append(" () (").append(EXISTSTRING)
                .append(" () ").append(formula).append("))");
        formula = temp;
        /* End of adding part */

        toReturn.append(formula);
        // toReturn.append("\n\n\"");
        // toReturn.append("\n\04");
        return toReturn;
    }

    @Override
    protected StringBuilder getIntegerSort() {
        return INTSTRING;
    }

    protected StringBuilder getBoolSort() {
        return BOOLSTRING;
    }

    @Override
    protected boolean isMultiSorted() {
        return false;
    }


    @Override
    protected StringBuilder translateFunction(StringBuilder name,
            ArrayList<StringBuilder> args) {
        return this.buildFunction(name, args);
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
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(GEQSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerGt(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(GTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerLeq(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(LEQSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerLt(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(LTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerMinus(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerMod(StringBuilder arg1,
            StringBuilder arg2) {
        return new StringBuilder("unknownOp");
    }

    @Override
    protected StringBuilder translateIntegerMult(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(MULTSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerPlus(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(PLUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerUnaryMinus(StringBuilder arg) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        StringBuilder n = new StringBuilder("0");
        args.add(n);
        args.add(arg);
        return buildFunction(MINUSSTRING, args);
    }

    @Override
    protected StringBuilder translateIntegerValue(long val) {
        return new StringBuilder("" + val);
    }

    @Override
    protected StringBuilder translateLogicalAll(StringBuilder var,
            StringBuilder type, StringBuilder form) {
        StringBuilder toReturn = new StringBuilder("(" + ALLSTRING + " ");
        toReturn.append("(" + var + ") " + form + ")");
        return toReturn;
    }

    @Override
    protected StringBuilder translateLogicalAnd(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(ANDSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalConstant(StringBuilder name) {
        return makeUnique(name);
    }

    @Override
    protected StringBuilder translateLogicalEquivalence(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);

        ArrayList<StringBuilder> argsrev = new ArrayList<StringBuilder>();
        argsrev.add(arg2);
        argsrev.add(arg1);

        ArrayList<StringBuilder> forms = new ArrayList<StringBuilder>();
        forms.add(buildFunction(IMPLYSTRING, args));
        forms.add(buildFunction(IMPLYSTRING, argsrev));
        return buildFunction(ANDSTRING, forms);
    }

    @Override
    protected StringBuilder translateLogicalExist(StringBuilder var,
            StringBuilder type, StringBuilder form) {
        StringBuilder toReturn = new StringBuilder("(" + EXISTSTRING + " ");
        toReturn.append("(" + var + ") " + form + ")");
        return toReturn;
    }

    @Override
    protected StringBuilder translateLogicalFalse() {
        return FALSESTRING;
    }

    @Override
    protected StringBuilder translateLogicalImply(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(IMPLYSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalNot(StringBuilder arg) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg);
        return this.buildFunction(NOTSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalOr(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(ORSTRING, args);
    }

    @Override
    protected StringBuilder translateLogicalTrue() {
        return TRUESTRING;
    }

    @Override
    protected StringBuilder translateLogicalVar(StringBuilder name) {
        return makeUnique(name);
    }

    @Override
    protected StringBuilder translateNull() {
        StringBuilder temp = new StringBuilder("(");
        temp.append(getNullName());
        temp.append(")");
        return temp;
    }

    @Override
    protected StringBuilder getNullName() {
        return NULLSTRING;
    }

    @Override
    protected StringBuilder translateNullSort() {
        return NULLSORTSTRING;
    }

    @Override
    protected StringBuilder translateLogicalIfThenElse(StringBuilder cond, StringBuilder ifterm,
            StringBuilder elseterm) {
        StringBuilder toReturn = this.translateLogicalImply(cond, ifterm);
        StringBuilder temp = this.translateLogicalNot(cond);
        temp = this.translateLogicalImply(temp, elseterm);
        toReturn = this.translateLogicalAnd(toReturn, temp);
        return toReturn;
    }

    @Override
    protected StringBuilder translateObjectEqual(StringBuilder arg1,
            StringBuilder arg2) {
        ArrayList<StringBuilder> args = new ArrayList<StringBuilder>();
        args.add(arg1);
        args.add(arg2);
        return this.buildFunction(EQSTRING, args);
    }

    @Override
    protected StringBuilder translatePredicate(StringBuilder name,
            ArrayList<StringBuilder> args) {
        return this.buildFunction(name, args);
    }

    @Override
    protected StringBuilder translatePredicateName(StringBuilder name) {
        return makeUnique(name);
    }

    @Override
    protected StringBuilder translateSort(String name, boolean isIntVal) {
        return makeUnique(new StringBuilder(name));
    }

    private StringBuilder buildFunction(StringBuilder name,
            ArrayList<StringBuilder> args) {
        StringBuilder toReturn = new StringBuilder();
        toReturn.append("(");
        toReturn.append(name);
        for (int i = 0; i < args.size(); i++) {
            toReturn.append(" ");
            toReturn.append(args.get(i));

        }
        toReturn.append(")");
        return toReturn;
    }


}
