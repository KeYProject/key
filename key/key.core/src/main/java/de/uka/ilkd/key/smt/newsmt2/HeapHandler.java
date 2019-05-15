package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.util.IdentityHashMap;
import java.util.Map;

public class HeapHandler implements SMTHandler {

    private static final String WELL_FORMED = "wellFormed";
    private static final String KEYSELECT = "keyselect";
    private static final String KEYSTORE = "keystore";
    private static final String KEYANON = "keyanon";
    private static final String KEYMEMSET = "keymemset";
    private static final String KEYCREATE = "keycreate";

    private Services services;
    private Map<Function, String> supportedFunctions =
            new IdentityHashMap<>();


    @Override
    public void init(Services services) {
        this.services = services;

        supportedFunctions.clear();
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        supportedFunctions.put(heapLDT.getAnon(), KEYANON);
        supportedFunctions.put(heapLDT.getWellFormed(), WELL_FORMED);
        supportedFunctions.put(heapLDT.getCreate(), KEYCREATE);
        supportedFunctions.put(heapLDT.getMemset(), KEYMEMSET);
        supportedFunctions.put(heapLDT.getStore(), KEYSTORE);
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return supportedFunctions.containsKey(op)
            || services.getTypeConverter().getHeapLDT().isSelectOp(op);
    }



    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        Operator op = term.op();

        if (services.getTypeConverter().getHeapLDT().getWellFormed() == op) {
            trans.addFromSnippets(WELL_FORMED);
            return new SExpr(WELL_FORMED, Type.BOOL, trans.translate(term.sub(0), Type.UNIVERSE));
        }

        if (supportedFunctions.containsKey(op)) {
            return trans.handleAsFunctionCall(supportedFunctions.get(op), term);
        }

        if (services.getTypeConverter().getHeapLDT().isSelectOp(op)) {
            trans.addFromSnippets(KEYSELECT);

            SExpr select = trans.handleAsFunctionCall(KEYSELECT, term);

            SortDependingFunction sdf = (SortDependingFunction) op;
            Sort dep = sdf.getSortDependingOn();

            if (dep == Sort.ANY) {
                return select;
            } else {
                return SExpr.castExpr(SExpr.sortExpr(dep), select);
            }
        }

        throw new SMTTranslationException("unreachable code");
    }

}
