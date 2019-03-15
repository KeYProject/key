package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class UpdateHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        if (op instanceof AbstractSortedOperator) {
            return ((AbstractSortedOperator) op).sort() == Sort.UPDATE;
        }
        return term.op() == UpdateApplication.UPDATE_APPLICATION;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        if (op instanceof AbstractSortedOperator &&
                ((AbstractSortedOperator) op).sort() == Sort.UPDATE) {
            if (op instanceof ElementaryUpdate) {
                SExpr rhsExpr = trans.translate(term.sub(0));
                return new SExpr("elementary-update", Type.UNIVERSE,
                        ((ElementaryUpdate) op).lhs().toString(), rhsExpr.toString());
            }
        } else if (term.op() == UpdateApplication.UPDATE_APPLICATION) {
            SExpr updateExpr = trans.translate(term.sub(0));
            SExpr targetExpr = trans.translate(term.sub(1));
            return new SExpr("apply-update", Type.UNIVERSE, updateExpr, targetExpr);
        }
        return null;
    }

}
