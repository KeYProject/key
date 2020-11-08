package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class QuantifierHandler implements SMTHandler {

    @Override
    public void init(Services services) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op == Quantifier.ALL || op == Quantifier.EX;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        SExpr matrix = trans.translate(term.sub(0), Type.BOOL);
        List<SExpr> vars = new ArrayList<>();
        List<SExpr> typeGuards = new ArrayList<>();
        for(QuantifiableVariable bv : term.boundVars()) {
            String varName = LogicalVariableHandler.VAR_PREFIX + bv.name();
            vars.add(new SExpr(varName, Type.NONE, "U"));
            // use "typeguard" instead of semantically equivalent "instanceof" to be able to distinguish
            // between typeguards (without direct counterpart on KeY sequent) and "real" instanceof uses
            // (this is needed for proof replay)
            typeGuards.add(new SExpr("typeguard", Type.BOOL,
                    new SExpr(varName), SExprs.sortExpr(bv.sort())));
        }
        // avoid additional and around single typeguard: (and (typeguard ...))
        SExpr typeGuard = typeGuards.size() == 1 ? typeGuards.get(0)
                                                 : new SExpr("and", Type.BOOL, typeGuards);
        SExpr typeGuardConnector;
        String smtOp;
        Operator op = term.op();
        if (op == Quantifier.ALL) {
            smtOp = "forall";
            typeGuardConnector = new SExpr("=>", Type.BOOL);
            trans.addFromSnippets("typeguard");
        } else if(op == Quantifier.EX) {
            smtOp = "exists";
            typeGuardConnector = new SExpr("and", Type.BOOL);
            trans.addFromSnippets("typeguard");
        } else {
            throw new SMTTranslationException("Unknown quantifier " + op);
        }

        matrix = new SExpr(typeGuardConnector, typeGuard, matrix);

        return new SExpr(smtOp, Type.BOOL, new SExpr(vars), matrix);

    }

}
