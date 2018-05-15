package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class UninterpretedSymbolsHandler implements SMTHandler {

    public final static String PREFIX = "ui_";

    @Override
    public void init(Services services) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return (op instanceof Function && term.boundVars().isEmpty())
            || op instanceof ProgramVariable;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        Operator op = term.op();
        String name = PREFIX + op.name().toString();
        if(!trans.isKnownSymbol(name)) {
            int a = op.arity();
            SExpr signature = new SExpr(Collections.nCopies(a, new SExpr("U")));
            trans.addDeclaration(
                    new SExpr("declare-fun", new SExpr(name), signature, new SExpr("U")));
            trans.addKnownSymbol(name);

            if (op.arity() > 0 && op instanceof SortedOperator) {
                SExpr axiom = funTypeAxiomFromTerm(term, name, trans);
                trans.addAxiom(axiom);
            }
        }

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        return new SExpr(name, Type.UNIVERSE, children);
    }

    public static SExpr funTypeAxiomFromTerm(Term term, String name, MasterHandler master) {
        SortedOperator op = (SortedOperator) term.op();
        List<SExpr> vars_U = new ArrayList<>();
        List<SExpr> vars = new ArrayList<>();
        for (int i = 0; i < op.arity(); ++i) {
            vars_U.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + i, Type.NONE, "U"));
            vars.add(new SExpr(LogicalVariableHandler.VAR_PREFIX + i));
        }

        List<SExpr> tos = new ArrayList<>();
        int i = 0;
        for (Sort sort : op.argSorts()) {
            master.addSort(sort);
            SExpr var = new SExpr(LogicalVariableHandler.VAR_PREFIX + i);
            SExpr to = new SExpr("typeof", var);
            tos.add(new SExpr("=", to, SExpr.sortExpr(sort)));
            ++i;
        }
        SExpr ante;
        if (tos.size() == 1) {
            ante = tos.get(0);
        } else {
            ante = new SExpr("and", tos);
        }
        SExpr cons = new SExpr("=", new SExpr("typeof", new SExpr(name, vars)),
                SExpr.sortExpr(op.sort()));
        SExpr matrix = new SExpr("=>", ante, cons);
        SExpr pattern = SExpr.patternSExpr(matrix, new SExpr(name, vars));
        SExpr axiom = new SExpr("forall", Type.BOOL, new SExpr(vars_U), pattern);
        return new SExpr("assert", axiom);
    }

}
