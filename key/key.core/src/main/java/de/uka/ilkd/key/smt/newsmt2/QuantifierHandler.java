package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.lang.SMTTermQuant.Quant;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import org.key_project.util.collection.ImmutableArray;

public class QuantifierHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(MasterHandler masterHandler, Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op == Quantifier.ALL || op == Quantifier.EX;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        term = collectQuantifications(term);

        SExpr matrix = trans.translate(term.sub(0), Type.BOOL);
        List<SExpr> vars = new ArrayList<>();
        List<SExpr> typeGuards = new ArrayList<>();
        for(QuantifiableVariable bv : term.boundVars()) {
            String varName = LogicalVariableHandler.VAR_PREFIX + bv.name();
            vars.add(new SExpr(varName, Type.NONE, "U"));
            typeGuards.add(SExprs.instanceOf(
                    new SExpr(varName), SExprs.sortExpr(bv.sort())));
        }
        SExpr typeGuard = SExprs.and(typeGuards);
        SExpr typeGuardConnector;
        String smtOp;
        Operator op = term.op();
        if(op == Quantifier.ALL) {
            smtOp = "forall";
            typeGuardConnector = new SExpr("=>", Type.BOOL);
        } else if(op == Quantifier.EX) {
            smtOp = "exists";
            typeGuardConnector = new SExpr("and", Type.BOOL);
        } else {
            throw new SMTTranslationException("Unknown quantifier " + op);
        }

        matrix = new SExpr(typeGuardConnector, typeGuard, matrix);
        matrix = SExprs.pullOutPatterns(matrix);

        return new SExpr(smtOp, Type.BOOL, new SExpr(vars), matrix);

    }

    private Term collectQuantifications(Term term) {
        Operator type = term.op();
        assert type == Quantifier.ALL || type == Quantifier.EX;
        Term current = term.sub(0);
        if (current.op() != type) {
            return term;
        }

        List<QuantifiableVariable> boundVars = term.boundVars().toList();
        while(current.op() == type) {
            boundVars.addAll(current.boundVars().toList());
            current = current.sub(0);
        }

        ImmutableArray<Term> subs = new ImmutableArray<>(current);
        ImmutableArray<QuantifiableVariable> bvars = new ImmutableArray<>(boundVars);
        return services.getTermFactory().createTerm(type, subs, bvars, null);
    }

}
