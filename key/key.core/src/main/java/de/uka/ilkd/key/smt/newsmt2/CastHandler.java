package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class CastHandler implements SMTHandler {

    private SortDependingFunction anyCast;

    @Override
    public void init(Services services) {
        this.anyCast = Sort.ANY.getCastSymbol(services);
    }

    @Override
    public boolean canHandle(Term term) {
        return term.op() instanceof SortDependingFunction &&
                ((SortDependingFunction) (term.op())).isSimilar(anyCast);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0));
        return new SExpr("cast", Type.UNIVERSE, inner, SExprs.sortExpr(op.getSortDependingOn()));
    }

}
