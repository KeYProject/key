package de.uka.ilkd.key.smt.newsmt2;

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
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
            op.arity();
            SExpr signature = new SExpr(Collections.nCopies(op.arity(), new SExpr("u")));
            trans.addDeclaration(new SExpr("declare-function",
                    new SExpr(name), signature, new SExpr("u")));
            trans.addKnownSymbol(name);
        }

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        return new SExpr(name, Type.UNIVERSE, children);
    }

}
