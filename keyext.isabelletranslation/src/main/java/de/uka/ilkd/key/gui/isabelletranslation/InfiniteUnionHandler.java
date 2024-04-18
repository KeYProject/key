package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class InfiniteUnionHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        supportedOperators.put(services.getTypeConverter().getLocSetLDT().getInfiniteUnion(), "SeqDef");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        String arg1 = "(\\<lambda>" + LogicalVariableHandler.makeVarRef(trans, term.boundVars().get(0).name().toString(), term.boundVars().get(0).sort()) + ". " +
                " to_any (" + trans.translate(term.sub(0)) + "))";

        return new StringBuilder("(\\<Union>").append(arg1).append(")");
    }
}
