package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

/**
 *  W O R K   I N   P R O G R E S S ! ! !
 *
 * This handler handles the seqDef binder function specially.
 *
 * @author Mattias Ulbrich
 */
public class SeqDefHandler implements SMTHandler {

    public static final String SEQ_DEF_PREFIX = "seqDef";
    private SeqLDT seqLDT;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) {
        seqLDT = services.getTypeConverter().getSeqLDT();
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == seqLDT.getSeqDef();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();

        assert (op == seqLDT.getSeqDef());

        Map<String, Object> state = trans.getTranslationState();
        Map<Term, SExpr> seqDefMap = (Map<Term, SExpr>)
          state.computeIfAbsent("SEQDEF_MAP",
                  x -> new LinkedHashMap<>());

        if (seqDefMap.containsKey(term)) {
            return seqDefMap.get(term);
        }

        int number = (int) state.getOrDefault("SEQDEF_COUNTER", 0) + 1;
        state.put("SEQDEF_COUNTER", number);
        String name = SEQ_DEF_PREFIX + number;

        Set<ParsableVariable> vars = Collections.newSetFromMap(new LinkedHashMap<>());
        collectVars(term, vars, DefaultImmutableSet.nil());

        trans.addDeclaration(makeFunctionDeclaration(name, vars));
        trans.addAxiom(makeTyping(name, vars, trans));
        trans.addAxiom(makeSeqGetDefinition(name, vars, term, trans));
        trans.addAxiom(makeSeqLenDefinition(name, vars, term, trans));

        return makeApplication(name, vars);
    }

    private void collectVars(Term term, Set<ParsableVariable> vars, ImmutableSet<QuantifiableVariable> boundVars) {

        Operator op = term.op();
        if (op instanceof LogicVariable && !boundVars.contains((QuantifiableVariable) op)) {
            vars.add((LogicVariable)op);
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

    private SExpr makeSeqLenDefinition(String function, Set<ParsableVariable> vars,
                                       Term term, MasterHandler trans) throws SMTTranslationException {
        List<SExpr> qvars = new ArrayList<>();
        List<SExpr> params = new ArrayList<>();
        for (ParsableVariable var : vars) {
            String name = var.name().toString();
            qvars.add(new SExpr(name, new SExpr("U")));
            params.add(new SExpr(name));
        }

        // \forall i; \forall params and(guards, i_range) -> seqGet(function(params), i) = term
        SExpr app = new SExpr(function, params);
        SExpr seqLen = new SExpr("seqLen", app);
        SExpr len = SExprs.minus(trans.translate(term.sub(1)), trans.translate(term.sub(0)));
        SExpr ite = SExprs.ite(SExprs.greaterEqual(len, SExprs.zero()), len, SExprs.zero());
        SExpr eq = SExprs.eq(seqLen, ite);
        SExpr forall = SExprs.forall(qvars, eq);
        return SExprs.assertion(forall);
    }

    private SExpr makeSeqGetDefinition(String function, Set<ParsableVariable> vars,
                                       Term term, MasterHandler trans) throws SMTTranslationException {

        List<SExpr> qvars = new ArrayList<>();
        List<SExpr> guards = new ArrayList<>();
        List<SExpr> params = new ArrayList<>();
        for (ParsableVariable var : vars) {
            String name = var.name().toString();
            qvars.add(new SExpr(name, new SExpr("U")));
            guards.add(SExprs.instanceOf(new SExpr(name), SExprs.sortExpr(var.sort())));
            params.add(new SExpr(name));
        }

        // \forall i; \forall params and(guards, i_range) -> seqGet(function(params), i) = term
        SExpr app = makeApplication(function, vars);
        SExpr i = new SExpr(term.boundVars().last().name().toString(), Type.UNIVERSE);
        qvars.add(new SExpr(i, new SExpr("U")));
        guards.add(SExprs.lessEqual(SExprs.zero(), i));
        guards.add(SExprs.lessThan(i, new SExpr("seqLen", Type.UNIVERSE, app)));
        SExpr smtTerm = trans.translate(term.sub(2));
        SExpr seqGet = new SExpr("seqGet", Type.UNIVERSE, app, i);
        SExpr imp = SExprs.imp(SExprs.and(guards), SExprs.eq(seqGet, smtTerm));
        SExpr forall = SExprs.forall(qvars, imp);
        return SExprs.assertion(forall);
    }

    private SExpr makeTyping(String name, Set<ParsableVariable> vars, MasterHandler master) throws SMTTranslationException {
        return HandlerUtil.funTypeAxiom(name, vars.size(), seqLDT.targetSort(), master);
    }

    private SExpr makeFunctionDeclaration(String name, Set<ParsableVariable> vars) {
        SExpr argTypes = new SExpr(Collections.nCopies(vars.size(), new SExpr("U")));
        SExpr decl = new SExpr("declare-fun", new SExpr(name), argTypes, new SExpr("U"));
        return decl;
    }

    private SExpr makeApplication(String name, Set<ParsableVariable> vars) {
        List<SExpr> args = new ArrayList<>();
        for (ParsableVariable var : vars) {
            args.add(new SExpr(var.name().toString()));
        }
        return new SExpr(name, Type.UNIVERSE, args);
    }
}