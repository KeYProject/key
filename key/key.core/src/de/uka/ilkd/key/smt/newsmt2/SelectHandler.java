package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class SelectHandler implements SMTHandler {

    public static final String HEAP = "Heap";
    public static final String WELL_FORMED = "wellFormed";
    public static final String KEYSELECT = "keyselect";
    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        return term.sort().toString().contains(HEAP)
            || term.toString().contains(WELL_FORMED)
            || services.getTypeConverter().getHeapLDT().isSelectOp(term.op());
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        if (term.sort().toString().contains(HEAP)) {
            String symbol = term.toString();
            if (!trans.isKnownSymbol(symbol)) {
                trans.addDeclaration(new SExpr(SExpr.DECLARE_CONST, term.toString(), "sort_heap"));
                trans.addKnownSymbol(symbol);
            }
            return new SExpr(term.toString(), Type.UNIVERSE);
        }

        if (term.toString().contains(WELL_FORMED)) {
            return new SExpr(WELL_FORMED, Type.BOOL, trans.translate(term.sub(0)));
        }

        SortDependingFunction op = (SortDependingFunction) term.op();
        Sort dep = op.getSortDependingOn();

        SExpr se1 = trans.translate(term.sub(0));
        SExpr se2 = trans.translate(term.sub(1));
        SExpr se3 = trans.translate(term.sub(2));

        if (dep == Sort.ANY) {
            return new SExpr(KEYSELECT, SExpr.Type.UNIVERSE, se1, se2, se3);
        }

        return SExpr.castExpr(SExpr.sortExpr(dep), new SExpr(KEYSELECT, SExpr.Type.UNIVERSE, se1, se2, se3));
    }
}
