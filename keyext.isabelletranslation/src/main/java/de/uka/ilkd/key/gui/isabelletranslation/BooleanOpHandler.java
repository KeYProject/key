package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

public class BooleanOpHandler implements IsabelleHandler {
    private final Map<Operator, StringBuilder> supportedOperators = new HashMap<>();

    {
        supportedOperators.put(Junctor.AND, new StringBuilder("\\<and>"));
        supportedOperators.put(Junctor.OR, new StringBuilder("\\<or>"));
        supportedOperators.put(Junctor.IMP, new StringBuilder("-->"));
        supportedOperators.put(Junctor.NOT, new StringBuilder("Not"));
        supportedOperators.put(Junctor.FALSE, new StringBuilder("False"));
        supportedOperators.put(Junctor.TRUE, new StringBuilder("True"));
        supportedOperators.put(Equality.EQV, new StringBuilder("\\<longleftrightarrow>"));
    }

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) {
        BooleanLDT ldt = services.getTypeConverter().getBooleanLDT();
        Operator logicFalse = ldt.getFalseConst();
        supportedOperators.put(logicFalse, new StringBuilder("False"));

        Operator logicTrue = ldt.getTrueConst();
        supportedOperators.put(logicTrue, new StringBuilder("True"));
        //TODO add boolean declarations
        masterHandler.addPredefinedSort(ldt.targetSort(), "bool");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        List<StringBuilder> children = trans.translate(term.subs());
        StringBuilder result = new StringBuilder();
        Operator op = term.op();
        result.append("((").append(supportedOperators.get(op)).append(")");
        for (StringBuilder child : children) {
            result.append(" ").append(child);
        }
        result.append(")");
        return result;
    }

}
