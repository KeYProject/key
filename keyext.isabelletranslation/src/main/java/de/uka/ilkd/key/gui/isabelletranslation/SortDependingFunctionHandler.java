package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.Properties;
import java.util.stream.Collectors;

public class SortDependingFunctionHandler implements IsabelleHandler {

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

        if (!trans.isKnownSort(dependentSort)) {
            trans.addGenericSort(dependentSort);
        }
        StringBuilder name;
        if (!trans.isKnownSymbol(term)) {
            name = LogicalVariableHandler.makeVarRef(trans, op.name().toString().split("::")[1], dependentSort);
            trans.addKnownSymbol(term, name);
        } else {
            name = trans.getKnownSymbol(term);
        }

        return getSortDependingFunctionRef(trans, term, op, name.toString());
    }

    static StringBuilder getSortDependingFunctionRef(IsabelleMasterHandler trans, Term term, SortDependingFunction op, String name) {
        StringBuilder ref = new StringBuilder("(").append(name).append("::");
        String parameterTypesDecl = op.argSorts().stream().map(trans::translateSortName).collect(Collectors.joining("=>"));
        ref.append(parameterTypesDecl).append("=>").append(trans.translateSortName(op.sort())).append(")");
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, op, ref.toString());
    }
}
