package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class SelectHandler implements SMTHandler {

    @Override
    public void init(Services services) {
        // nothing to do here
    }

    @Override
    public boolean canHandle(Term term) {
        return term.op().toString().contains("select"); // TODO igittigitt
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        Sort dep = op.getSortDependingOn();
        String funName = dep.toString() + "::select";
        SExpr se1 = trans.translate(term.sub(0));
        SExpr se2 = trans.translate(term.sub(1));
        SExpr se3 = trans.translate(term.sub(2));

        if (!trans.isKnownSymbol(funName)) {
            trans.addAxiom(UninterpretedSymbolsHandler.funTypeAxiomFromTerm(term, funName));
            trans.addKnownSymbol(funName);
        }

        if (dep.name().toString().equals("int")) { //TODO
            return new SExpr(funName, Type.INT, se1, se2, se3);
        } else if (dep.name().toString().equals("boolean")) { //TODO
            return new SExpr(funName, Type.BOOL, se1, se2, se3);
        } else {
            return new SExpr(funName, Type.UNIVERSE, se1, se2, se3);
        }
    }
}
