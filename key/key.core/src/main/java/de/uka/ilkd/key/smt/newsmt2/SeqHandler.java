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
import java.util.HashMap;
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
            return new SExpr(SEQ_LEN, SExpr.Type.INT, trans.translate(term.subs()));
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
                return SExpr.castExpr(SExpr.sortExpr(dep), get);
            }
        }

        throw new SMTTranslationException("unreachable code");
    }

    private boolean isSeqGet(Operator op) {
        return op instanceof SortDependingFunction && op.name().equals(SEQGET_NAME);
    }
}