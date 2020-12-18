package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.Properties;

@Deprecated
public class LocSetHandler extends SMTFunctionsHandler {

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) {
        super.init(masterHandler, services, handlerSnippets);

        LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        addOperator(locSetLDT.getElementOf(), Type.BOOL);
        addOperator(locSetLDT.getFreshLocs());
        addOperator(locSetLDT.getEmpty());
        addOperator(locSetLDT.getUnion(), "keyunion");
    }
}
