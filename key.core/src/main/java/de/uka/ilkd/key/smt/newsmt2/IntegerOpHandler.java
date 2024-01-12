/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;

/**
 * This SMT translation handler takes care of integer expressions.
 *
 * This includes the unary and binary integer operations and relational operations.
 *
 * @author Jonas Schiffl
 */
public class IntegerOpHandler implements SMTHandler {

    /** to indicate that an expression holds a value of type Int. */
    public static final Type INT = new Type("Int", "i2u", "u2i");

    public static final SMTHandlerProperty.BooleanProperty PROPERTY_PRESBURGER =
        new BooleanProperty("Presburger", "Limit arithmetics to Presburger arithmetic (LIA)",
            "Some tools only support linear arithmetic, others "
                + "may handle this more efficiently.");

    private final Map<Operator, String> supportedOperators = new HashMap<>();
    private final Set<Operator> predicateOperators = new HashSet<>();
    private Function mul;
    private boolean limitedToPresbuger;
    private IntegerLDT integerLDT;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        supportedOperators.clear();
        this.integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getAdd(), "+");
        mul = integerLDT.getMul();
        supportedOperators.put(mul, "*");
        supportedOperators.put(integerLDT.getSub(), "-");
        supportedOperators.put(integerLDT.getDiv(), "div");
        supportedOperators.put(integerLDT.getNeg(), "-");

        supportedOperators.put(integerLDT.getLessOrEquals(), "<=");
        predicateOperators.add(integerLDT.getLessOrEquals());
        supportedOperators.put(integerLDT.getLessThan(), "<");
        predicateOperators.add(integerLDT.getLessThan());
        supportedOperators.put(integerLDT.getGreaterOrEquals(), ">=");
        predicateOperators.add(integerLDT.getGreaterOrEquals());
        supportedOperators.put(integerLDT.getGreaterThan(), ">");
        predicateOperators.add(integerLDT.getGreaterThan());

        masterHandler.addDeclarationsAndAxioms(handlerSnippets);

        // sort_int is defined here, declare it as already defined
        masterHandler.addKnownSymbol("sort_int");
        masterHandler.addSort(integerLDT.targetSort());

        this.limitedToPresbuger = PROPERTY_PRESBURGER.get(masterHandler.getTranslationState());
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public Capability canHandle(Term term) {
        Operator op = term.op();
        if (!supportedOperators.containsKey(op)) {
            return Capability.UNABLE;
        }

        if (!limitedToPresbuger || op != mul) {
            return Capability.YES_THIS_OPERATOR;
        }

        if (!isIntLiteral(term.sub(0))) {
            isIntLiteral(term.sub(1));
        }

        return Capability.YES_THIS_INSTANCE;
    }

    private boolean isIntLiteral(Term term) {
        return term.op() == integerLDT.getNumberSymbol();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        List<SExpr> children = trans.translate(term.subs(), IntegerOpHandler.INT);
        Operator op = term.op();
        String smtOp = supportedOperators.get(op);
        assert smtOp != null;

        Type resultType;
        if (predicateOperators.contains(op)) {
            resultType = Type.BOOL;
        } else {
            resultType = IntegerOpHandler.INT;
        }

        return new SExpr(smtOp, resultType, children);
    }

    /*
     * There is a switch for limiting to presburger arithmetic.
     */
    @Override
    public List<SMTHandlerProperty<?>> getProperties() {
        return List.of(PROPERTY_PRESBURGER);
    }

}
