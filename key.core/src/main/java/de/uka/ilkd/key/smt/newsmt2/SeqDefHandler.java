/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * This handler handles the seqDef binder function specially.
 *
 * For every applicatin of seqDef a new function symbol is introduced which captures its meaning.
 *
 * If there are variables used inside the seqDef expression, the symbol is a function and these
 * variables are used as its arguments.
 *
 * Two axioms are added: One defining the length of the defined sequence, and one defining the
 * entries of the sequence.
 *
 * <bold> THIS IS STILL WORK IN PROGRESS and probably not yet correct nor working. </bold>
 *
 * @author Mattias Ulbrich
 */
public class SeqDefHandler implements SMTHandler {

    private static final String SEQLEN = DefinedSymbolsHandler.PREFIX + "seqLen";
    private static final String SEQGET = DefinedSymbolsHandler.PREFIX + "seqGet";

    public static final String SEQ_DEF_PREFIX = "seqDef";
    private SeqLDT seqLDT;
    private boolean enabled;
    private TermFactory termFactory;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        enabled = !HandlerUtil.PROPERTY_NOBINDERS.get(masterHandler.getTranslationState());
        seqLDT = services.getTypeConverter().getSeqLDT();
        termFactory = services.getTermFactory();
    }

    @Override
    public boolean canHandle(Operator op) {
        return enabled && op == seqLDT.getSeqDef();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();

        assert (op == seqLDT.getSeqDef());

        Map<String, Object> state = trans.getTranslationState();
        Map<Term, SExpr> seqDefMap =
            (Map<Term, SExpr>) state.computeIfAbsent("SEQDEF_MAP", x -> new LinkedHashMap<>());

        for (Entry<Term, SExpr> entry : seqDefMap.entrySet()) {
            if (entry.getKey().equalsModRenaming(term)) {
                return entry.getValue();
            }
        }

        int number = (int) state.getOrDefault("SEQDEF_COUNTER", 0) + 1;
        state.put("SEQDEF_COUNTER", number);
        String name = SEQ_DEF_PREFIX + number;

        Set<ParsableVariable> vars = Collections.newSetFromMap(new LinkedHashMap<>());
        collectVars(term, vars, DefaultImmutableSet.nil());

        trans.introduceSymbol("seqGet");
        trans.introduceSymbol("seqLen");

        trans.addDeclaration(makeFunctionDeclaration(name, vars));
        trans.addAxiom(makeTyping(name, vars, trans));
        trans.addAxiom(makeSeqGetDefinition(name, vars, term, trans));
        trans.addAxiom(makeSeqLenDefinition(name, vars, term, trans));

        SExpr result = makeTermApplication(trans, name, vars);
        seqDefMap.put(term, result);

        return result;
    }

    private void collectVars(Term term, Set<ParsableVariable> vars,
            ImmutableSet<QuantifiableVariable> boundVars) {

        Operator op = term.op();
        if (op instanceof LogicVariable && !boundVars.contains((QuantifiableVariable) op)) {
            vars.add((LogicVariable) op);
            return;
        }

        if (op instanceof ProgramVariable) {
            vars.add((ProgramVariable) op);
            return;
        }

        ImmutableSet<QuantifiableVariable> localBind = boundVars;
        for (QuantifiableVariable boundVar : term.boundVars()) {
            localBind = localBind.add(boundVar);
        }

        for (Term sub : term.subs()) {
            collectVars(sub, vars, localBind);
        }

    }

    private SExpr makeSeqLenDefinition(String function, Set<ParsableVariable> vars, Term term,
            MasterHandler trans) throws SMTTranslationException {
        List<SExpr> qvars = new ArrayList<>();
        List<SExpr> params = new ArrayList<>();
        for (ParsableVariable var : vars) {
            String name = var.name().toString();
            qvars.add(LogicalVariableHandler.makeVarDecl(name, var.sort()));
            SExpr varRef = LogicalVariableHandler.makeVarRef(name, var.sort());
            params.add(SExprs.coerce(varRef, Type.UNIVERSE));
        }

        // \forall freevars; seqLen(function(params)) = \if(up-lo>=0) \then(up-lo) \else 0
        SExpr app = new SExpr(function, params);
        SExpr seqLen = new SExpr(SEQLEN, app);
        SExpr len = SExprs.minus(trans.translate(term.sub(1), IntegerOpHandler.INT),
            trans.translate(term.sub(0), IntegerOpHandler.INT));
        SExpr ite = SExprs.ite(SExprs.greaterEqual(len, SExprs.ZERO), len, SExprs.ZERO);
        SExpr eq = SExprs.eq(seqLen, ite);
        SExpr forall = SExprs.forall(qvars, eq);
        return SExprs.assertion(forall);
    }

    private SExpr makeSeqGetDefinition(String function, Set<ParsableVariable> vars, Term term,
            MasterHandler trans) throws SMTTranslationException {

        List<SExpr> qvars = new ArrayList<>();
        List<SExpr> guards = new ArrayList<>();
        List<SExpr> params = new ArrayList<>();
        for (ParsableVariable var : vars) {
            String name = var.name().toString();
            qvars.add(LogicalVariableHandler.makeVarDecl(name, var.sort()));

            trans.addSort(var.sort());
            SExpr smtVar = new SExpr(LogicalVariableHandler.VAR_PREFIX + name);
            if (!var.sort().name().equals(IntegerLDT.NAME)) {
                guards.add(SExprs.instanceOf(smtVar, SExprs.sortExpr(var.sort())));
            }
            params.add(smtVar);
        }

        // \forall i; \forall params;
        // and(guards, i_range) -> seqGet(function(params), i) = let i = i + lo in term
        SExpr app = makeApplication(function, vars);
        QuantifiableVariable last = term.boundVars().last();
        String name = last.name().toString();
        Sort sort = last.sort();
        SExpr i = LogicalVariableHandler.makeVarRef(name, sort);
        qvars.add(LogicalVariableHandler.makeVarDecl(name, sort));
        guards.add(SExprs.lessEqual(SExprs.ZERO, i));
        SExpr upper = trans.translate(term.sub(1), IntegerOpHandler.INT);
        SExpr lower = trans.translate(term.sub(0), IntegerOpHandler.INT);
        SExpr len = SExprs.minus(upper, lower);
        guards.add(SExprs.lessThan(i, len));
        SExpr smtTerm = trans.translate(term.sub(2), Type.UNIVERSE);
        SExpr replacedSMTTerm = SExprs.let(LogicalVariableHandler.VAR_PREFIX + name,
            SExprs.coerce(SExprs.plus(i, lower), IntegerOpHandler.INT), smtTerm);
        SExpr seqGet = new SExpr(SEQGET, Type.UNIVERSE, app, new SExpr("i2u", i));
        SExpr imp = SExprs.imp(SExprs.and(guards), SExprs.eq(seqGet, replacedSMTTerm));
        SExpr forall = SExprs.forall(qvars, imp);
        return SExprs.assertion(forall);
    }

    private SExpr makeTyping(String name, Set<ParsableVariable> vars, MasterHandler master)
            throws SMTTranslationException {
        return HandlerUtil.funTypeAxiom(name, vars.size(), seqLDT.targetSort(), master);
    }

    private SExpr makeFunctionDeclaration(String name, Set<ParsableVariable> vars) {
        SExpr argTypes = new SExpr(Collections.nCopies(vars.size(), new SExpr("U")));
        SExpr decl = new SExpr("declare-fun", new SExpr(name), argTypes, new SExpr("U"));
        return decl;
    }

    private SExpr makeApplication(String name, Set<ParsableVariable> vars)
            throws SMTTranslationException {
        List<SExpr> args = new ArrayList<>();
        for (ParsableVariable var : vars) {
            SExpr varRef = LogicalVariableHandler.makeVarRef(var.name().toString(), var.sort());
            args.add(SExprs.coerce(varRef, Type.UNIVERSE));
        }
        return new SExpr(name, Type.UNIVERSE, args);
    }

    private SExpr makeTermApplication(MasterHandler trans, String name, Set<ParsableVariable> vars)
            throws SMTTranslationException {
        List<SExpr> args = new ArrayList<>();
        for (ParsableVariable var : vars) {
            SExpr ref = trans.translate(termFactory.createTerm(var));
            args.add(SExprs.coerce(ref, Type.UNIVERSE));
        }
        return new SExpr(name, Type.UNIVERSE, args);
    }

    /*
     * This handler should not go to work if binders have been deactivated.
     */
    @Override
    public List<SMTHandlerProperty<?>> getProperties() {
        return List.of(HandlerUtil.PROPERTY_NOBINDERS);
    }

}
