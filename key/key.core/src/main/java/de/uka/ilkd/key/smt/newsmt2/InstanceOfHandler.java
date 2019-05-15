package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.ExactInstanceof;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class InstanceOfHandler implements SMTHandler {

    private Services services;
    private SortDependingFunction exactInstanceOfOp;
    private SortDependingFunction instanceOfOp;

    @Override
    public void init(Services services) {
        this.services = services;
        this.instanceOfOp = Sort.ANY.getInstanceofSymbol(services);
        this.exactInstanceOfOp = Sort.ANY.getExactInstanceofSymbol(services);
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        if (op instanceof SortDependingFunction) {
            SortDependingFunction sdf = (SortDependingFunction) op;
            return exactInstanceOfOp.isSimilar(sdf) || instanceOfOp.isSimilar(sdf);
        }
        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0));
        if (exactInstanceOfOp.isSimilar(op)) {
            trans.addFromSnippets("exactinstanceof");
            SExpr res = new SExpr("exactinstanceof", Type.BOOL, inner,
                SExpr.sortExpr(op.getSortDependingOn()));
            return res;
        } else if (instanceOfOp.isSimilar(op)) {
            trans.addFromSnippets("instanceof");
            SExpr res = new SExpr("instanceof", Type.BOOL, inner,
                SExpr.sortExpr(op.getSortDependingOn()));
            return res;
        } else {
            // MU Review. return null is a very bad idea unless you want to
            // get strange NPE somewhere later down the stream.
            // return null;
            throw new RuntimeException("unexpected case in instanceof-handling");
        }
    }
}
