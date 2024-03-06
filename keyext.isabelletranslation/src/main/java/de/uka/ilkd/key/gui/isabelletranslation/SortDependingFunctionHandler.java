package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.Properties;

import static de.uka.ilkd.key.gui.isabelletranslation.UninterpretedSymbolsHandler.getFunctionTranslation;

public class SortDependingFunctionHandler implements IsabelleHandler {
    private final String PREFIX = "var_";

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {

    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof SortDependingFunction);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        assert term.op() instanceof SortDependingFunction;
        SortDependingFunction op = (SortDependingFunction) term.op();
        Sort dependentSort = op.getSortDependingOn();

        if (!trans.isKnownSort(op.getSortDependingOn())) {
            trans.addSort(dependentSort);
        }

        String name = PREFIX + op.name().toString().split("::")[1];
        if (!trans.isKnownSymbol(term)) {
            trans.addKnownSymbol(term, new StringBuilder(name));
        }
        return getFunctionTranslation(trans, term, op, name);
    }
}
