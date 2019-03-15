package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class CastHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        if (!(op instanceof SortDependingFunction)) {
            return false;
        }
        SortDependingFunction dep = term.sort().getCastSymbol(services);
        return term.op() instanceof SortDependingFunction && ((SortDependingFunction) (term.op())).isSimilar(dep);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0));
        return new SExpr("cast", Type.UNIVERSE, inner, SExpr.sortExpr(op.getSortDependingOn()));
    }

}
