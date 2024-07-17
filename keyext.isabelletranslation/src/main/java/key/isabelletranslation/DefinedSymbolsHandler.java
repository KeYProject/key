package key.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.JFunction;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.smt.SMTTranslationException;
import org.key_project.logic.op.SortedOperator;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class DefinedSymbolsHandler implements IsabelleHandler {
    Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        Namespace<JFunction> functionNamespace = services.getNamespaces().functions();
        Map<String, String> definedFunctions = new HashMap<>();
        definedFunctions.put("null", "null");
        definedFunctions.put("length", "obj_length");
        definedFunctions.put("arr", "arr");
        definedFunctions.put("wellFormed", "wellFormed");
        definedFunctions.put("anon", "anon");
        definedFunctions.put("store", "store");
        definedFunctions.put("create", "create");

        //Seq functions
        definedFunctions.put("seqLen", "seqLen");
        definedFunctions.put("seqIndexOf", "seqIndexOf");
        definedFunctions.put("seqGetOutside", "seqGetOutside");
        definedFunctions.put("seqEmpty", "seqEmpty");
        definedFunctions.put("seqSingleton", "seqSingleton");
        definedFunctions.put("seqConcat", "seqConcat");
        definedFunctions.put("seqSub", "seqSub");
        definedFunctions.put("seqPerm", "seqPerm");
        definedFunctions.put("seqNPerm", "seqNPerm");
        definedFunctions.put("seqSwap", "seqSwap");
        definedFunctions.put("seqRemove", "seqRemove");
        definedFunctions.put("seqReverse", "seqReverse");


        //LocSet functions
        definedFunctions.put("elementOf", "elementOf");
        definedFunctions.put("subset", "subset");
        definedFunctions.put("disjoint", "disjoint");
        definedFunctions.put("empty", "empty");
        definedFunctions.put("allLocs", "allLocs");
        definedFunctions.put("singleton", "singleton");
        definedFunctions.put("union", "union");
        definedFunctions.put("intersect", "intersect");
        definedFunctions.put("setMinus", "setMinus");
        definedFunctions.put("allFields", "allFields");
        definedFunctions.put("allObjects", "allObjects");
        definedFunctions.put("arrayRange", "arrayRange");

        Map<String, String> definedSortDependingFunctions = new HashMap<>();
        definedSortDependingFunctions.put("select", "select");
        definedSortDependingFunctions.put("cast", "cast");
        definedSortDependingFunctions.put("seqGet", "seqGet");

        for (String name : definedFunctions.keySet()) {
            Function function = functionNamespace.lookup(name);
            if (function != null)
                supportedOperators.put(function, definedFunctions.get(name));
        }

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
        if (term.op() instanceof SortDependingFunction) {
            return SortDependingFunctionHandler.getSortDependingFunctionRef(trans, term, (SortDependingFunction) term.op(),
                    supportedOperators.get(term.op()));
        }
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, (SortedOperator) term.op(), supportedOperators.get(term.op()));
    }
}
