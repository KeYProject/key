package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SeqHandler extends SMTFunctionsHandler {

    private SeqLDT seqLDT;

    @Override
    public void init(Services services) {
        seqLDT = services.getTypeConverter().getSeqLDT();
        addOperator(seqLDT.getSeqLen(), Type.INT);
        addOperator(seqLDT.getSeqConcat());
        addOperator(seqLDT.getSeqEmpty());
        addOperator(seqLDT.getSeqSingleton());
        addCastingOperator(seqLDT.getSeqGet(Sort.ANY, services));
    }

    @Override
    public boolean canHandle(Term term) {
        return super.canHandle(term);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();

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

        return super.handle(trans, term);
    }
}