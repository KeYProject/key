package key.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class InstanceOperatorHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        Namespace<Function> functionNamespace = services.getNamespaces().functions();
        Map<String, String> definedSortDependingFunctions = new HashMap<>();

        definedSortDependingFunctions.put("instance", "instanceof");
        definedSortDependingFunctions.put("exactInstance", "exactInstance");

        for (Function function : functionNamespace.elements()) {
            if (!(function instanceof SortDependingFunction))
                continue;
            String funName = function.name().toString().split("::")[1];
            for (String name : definedSortDependingFunctions.keySet()) {
                if (funName.equals(name)) {
                    supportedOperators.put(function, definedSortDependingFunctions.get(name));
                }
            }
        }
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        String functionName = supportedOperators.get(op);
        String dependingSortTypeName = trans.translateSortName(op.getSortDependingOn()) + "_type";

        StringBuilder result = new StringBuilder("(");
        result.append("(").append(functionName).append(") ");
        result.append(trans.translate(term.sub(0))).append(" ");
        result.append(dependingSortTypeName).append(")");

        return result;
    }
}
