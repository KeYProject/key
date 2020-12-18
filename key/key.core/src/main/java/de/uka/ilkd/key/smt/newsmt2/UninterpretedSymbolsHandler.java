package de.uka.ilkd.key.smt.newsmt2;

import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.BOOL;
import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.UNIVERSE;

public class UninterpretedSymbolsHandler implements SMTHandler {

    public final static String PREFIX = "u_";

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) {
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
        SortedOperator op = (SortedOperator) term.op();
        String name = PREFIX + op.name().toString();
        if(!trans.isKnownSymbol(name)) {
            trans.addDeclaration(HandlerUtil.funDeclaration(op, name));
            if(op.sort() != Sort.FORMULA) {
                trans.addAxiom(HandlerUtil.funTypeAxiom(op, name, trans));
            }
            trans.addKnownSymbol(name);
        }

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        SExpr.Type exprType = term.sort() == Sort.FORMULA ? BOOL : UNIVERSE;
        return new SExpr(name, exprType, children);
    }

}
