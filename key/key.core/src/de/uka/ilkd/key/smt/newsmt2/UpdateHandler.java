package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

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
        return null;
    }

}
