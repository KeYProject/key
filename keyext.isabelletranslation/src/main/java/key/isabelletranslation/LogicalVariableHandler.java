package key.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

import java.util.Properties;

public class LogicalVariableHandler implements IsabelleHandler {

    static final String VAR_PREFIX = "var_";

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) {

    }

    @Override
    public boolean canHandle(Operator op) {
        return op instanceof LogicVariable;
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        Sort sort = term.sort();
        if (trans.isNewSort(sort)) {
            trans.addGenericSort(sort);
        }
        return makeVarRef(trans, term.toString(), sort);
    }

    public static StringBuilder makeVarRef(IsabelleMasterHandler trans, String name, Sort sort) {
        StringBuilder result = new StringBuilder("(");
        result.append(VAR_PREFIX).append(name).append("::").append(trans.translateSortName(sort)).append(")");
        return result;
    }
}
