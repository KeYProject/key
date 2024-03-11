package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class BSumHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        supportedOperators.clear();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getBsum(), "\\<Sum>");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        StringBuilder result = new StringBuilder("(");
        result.append(supportedOperators.get(term.op()));
        for (QuantifiableVariable bv : term.boundVars()) {
            Sort sort = bv.sort();
            result.append(" ").append(LogicalVariableHandler.makeVarRef(trans, bv.name().toString(), sort));
            if (!trans.isKnownSort(sort)) {
                trans.addGenericSort(sort);
            }
        }
        result.append("=");
        result.append(trans.translate(term.sub(0))).append("..<").append(trans.translate(term.sub(1))).append(". ");
        result.append(trans.translate(term.sub(2))).append(")");
        return result;
    }
}
