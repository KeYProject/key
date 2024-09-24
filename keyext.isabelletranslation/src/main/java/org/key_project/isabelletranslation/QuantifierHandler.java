package org.key_project.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import org.key_project.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class QuantifierHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        supportedOperators.put(Quantifier.ALL, "\\<forall>");
        supportedOperators.put(Quantifier.EX, "\\<exists>");
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
            if (trans.isNewSort(sort)) {
                trans.addGenericSort(sort);
            }
        }
        result.append(". (");
        result.append(trans.translate(term.sub(0))).append("))");
        return result;
    }

}