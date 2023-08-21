/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import org.key_project.util.collection.ImmutableArray;

/**
 * This SMT translation handler takes care of quantifier formulas using existential or universal
 * quantifiers.
 *
 * It is non-trivial because triggers need to be dealt with and type guards must be added.
 *
 * @author Jonas Schiffl
 * @author Mattias Ulbrich
 */
public class QuantifierHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Operator op) {
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
        for (QuantifiableVariable bv : term.boundVars()) {
            Sort sort = bv.sort();
            String name = bv.name().toString();
            vars.add(LogicalVariableHandler.makeVarDecl(name, sort));
            if (!sort.equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
                // Special casing integer quantification: Avoid conversion to "U".
                // Caution: Must be in sync with logical variable treatment.
                trans.addSort(sort);
                typeGuards.add(SExprs.instanceOf(
                    new SExpr(LogicalVariableHandler.VAR_PREFIX + name), SExprs.sortExpr(sort)));
            }
        }
        SExpr typeGuard = SExprs.and(typeGuards);
        String smtOp;
        Operator op = term.op();
        if (op == Quantifier.ALL) {
            smtOp = "forall";
            matrix = SExprs.imp(typeGuard, matrix);
        } else if (op == Quantifier.EX) {
            smtOp = "exists";
            typeGuards.add(matrix);
            matrix = SExprs.and(typeGuards);
        } else {
            throw new SMTTranslationException("Unknown quantifier " + op);
        }

        matrix = SExprs.patternSExpr(matrix, new ArrayList<>(triggers));

        return new SExpr(smtOp, Type.BOOL, new SExpr(vars), matrix);
    }

    private void collectTriggers(Term term, Set<Term> triggers) {
        if (term.containsLabel(DefinedSymbolsHandler.TRIGGER_LABEL)) {
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
        while (current.op() == type) {
            boundVars.addAll(current.boundVars().toList());
            current = current.sub(0);
        }

        ImmutableArray<Term> subs = new ImmutableArray<>(current);
        ImmutableArray<QuantifiableVariable> bvars = new ImmutableArray<>(boundVars);
        return services.getTermFactory().createTerm(type, subs, bvars, null);
    }

}
