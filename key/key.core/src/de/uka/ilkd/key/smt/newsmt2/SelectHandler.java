package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

public class SelectHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        return services.getTypeConverter().getHeapLDT().isSelectOp(term.op());
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        Sort dep = op.getSortDependingOn();

        SExpr se1 = trans.translate(term.sub(0));
        SExpr se2 = trans.translate(term.sub(1));
        SExpr se3 = trans.translate(term.sub(2));

        if (dep == Sort.ANY) {
            return new SExpr("keyselect", se1, se2, se3);
        }

        return SExpr.castExpr(SExpr.sortExpr(dep), new SExpr("keyselect", se1, se2, se3));
    }
}
