package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SeqHandler implements SMTHandler {

    private static final String SEQ_CONCAT = "seqConcat";
    private static final String SEQ_LEN = "seqLen";
    private static final String SEQ_DEF = "seqDef";
    private static final String SEQ_EMPTY = "seqEmpty";
    private static final String SEQ_SINGLETON = "seqSingleton";
    private static final Name SEQGET_NAME = SeqLDT.SEQGET_NAME;
    private static final String SEQGET = SEQGET_NAME.toString();
    private SeqLDT seqLDT;

    private Map<Operator, String> supportedOperators;

    private static int numOfSeqVars = 0;

    @Override
    public void init(Services services) throws IOException {
        seqLDT = services.getTypeConverter().getSeqLDT();
        this.supportedOperators = new HashMap<>();
        supportedOperators.put(seqLDT.getSeqConcat(), SEQ_CONCAT);
        supportedOperators.put(seqLDT.getSeqLen(), SEQ_LEN);
        supportedOperators.put(seqLDT.getSeqDef(), SEQ_DEF);
        supportedOperators.put(seqLDT.getSeqEmpty(), SEQ_EMPTY);
        supportedOperators.put(seqLDT.getSeqSingleton(), SEQ_SINGLETON);
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return supportedOperators.containsKey(op)
                || isSeqGet(op);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();

        if (op == seqLDT.getSeqLen()) {
            trans.addFromSnippets(SEQ_LEN);
            return new SExpr(SEQ_LEN, SExpr.Type.INT, trans.translate(term.subs()));
        }

        if (op == seqLDT.getSeqDef()) { // TODO substituting the sequence variable in the function
//            trans.addFromSnippets(SEQ_DEF);
//            List<SExpr> children = new ArrayList<>();
//            String sv = "seqVar_" + numOfSeqVars;
//            SExpr seqVar = new SExpr(sv);
//            trans.addKnownSymbol(sv);
//            trans.addDeclaration(new SExpr("declare-fun", SExpr.Type.UNIVERSE, new SExpr(sv), new SExpr(""), new SExpr("U")));
//            children.add(seqVar);
//            numOfSeqVars++;
//            children.add(trans.translate(term.sub(0), SExpr.Type.INT));
//            children.add(trans.translate(term.sub(1), SExpr.Type.INT));
//            children.add(trans.translate(term.sub(2), SExpr.Type.UNIVERSE));
//            return new SExpr(SEQ_DEF, SExpr.Type.UNIVERSE, children);
        }

        if (supportedOperators.containsKey(op)) {
            trans.addFromSnippets(supportedOperators.get(op));
            return trans.handleAsFunctionCall(supportedOperators.get(op), term);
        }

        if (isSeqGet(op)) {
            trans.addFromSnippets(SEQGET);
            SExpr get = trans.handleAsFunctionCall(SEQGET, term);

            SortDependingFunction sdf = (SortDependingFunction) op;
            Sort dep = sdf.getSortDependingOn();

            if (dep == Sort.ANY) {
                return get;
            } else {
                return SExprs.castExpr(SExprs.sortExpr(dep), get);
            }
        }

        throw new SMTTranslationException("Unsupported term: " + term);
    }

    private boolean isSeqGet(Operator op) {
        return op instanceof SortDependingFunction &&
                op.name().toString().endsWith("::" + SEQGET_NAME.toString());
    }
}