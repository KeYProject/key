package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class NumberConstantsHandler implements SMTHandler {

    private Function numberSymbol;
    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
        numberSymbol = services.getTypeConverter().getIntegerLDT().getNumberSymbol();
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op == numberSymbol;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        String string = AbstractTermTransformer.convertToDecimalString(term, services);
        return new SExpr(string, Type.INT);
    }

}
