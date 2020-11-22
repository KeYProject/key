package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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

        Set<Term> triggerTerms = new HashSet<>();
        collectTriggers(term, triggerTerms);

        Set<SExpr> triggers = new HashSet<>();
        for (Term triggerTerm : triggerTerms) {
            triggers.add(trans.translate(triggerTerm));
        }

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
        if(op == Quantifier.ALL) {
            smtOp = "forall";
            typeGuardConnector = new SExpr("=>", Type.BOOL);
        } else if(op == Quantifier.EX) {
            smtOp = "exists";
            typeGuardConnector = new SExpr("and", Type.BOOL);
        } else {
            throw new SMTTranslationException("Unknown quantifier " + op);
        }

        trans.addFromSnippets("typeguard");
        trans.setTypeguardAxiomsNeeded(true);

        matrix = new SExpr(typeGuardConnector, typeGuard, matrix);
        matrix = SExprs.patternSExpr(matrix, triggers);

        return new SExpr(smtOp, Type.BOOL, new SExpr(vars), matrix);
    }

    private void collectTriggers(Term term, Set<Term> triggers) {
        if(term.containsLabel(DefinedSymbolsHandler.TRIGGER_LABEL)) {
            triggers.add(term);
        }
        term.subs().forEach(x -> collectTriggers(x, triggers));
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
