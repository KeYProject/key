package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;

public class SeqHandler implements SMTHandler {
    private Services services;

    @Override
    public void init(Services services) throws IOException {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
        return op == seqLDT.getSeqConcat()
                || op == seqLDT.getSeqDef()
                || op == seqLDT.getSeqEmpty()
                || op == seqLDT.getSeqLen(); //TODO js etc...
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        return null;
    }
}