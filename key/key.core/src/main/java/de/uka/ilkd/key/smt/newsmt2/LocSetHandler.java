package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.IdentityHashMap;
import java.util.Map;

public class LocSetHandler extends SMTFunctionsHandler {

    @Override
    public void init(Services services) {
        super.init(services);

        LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        addOperator(locSetLDT.getElementOf(), Type.BOOL);
        addOperator(locSetLDT.getFreshLocs());
        addOperator(locSetLDT.getEmpty());
        addOperator(locSetLDT.getUnion(), "keyunion");
    }
}
