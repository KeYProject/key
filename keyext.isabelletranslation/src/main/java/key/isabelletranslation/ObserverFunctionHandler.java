package key.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import org.key_project.logic.Term;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ObserverFunctionHandler implements IsabelleHandler {
    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {

    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof ObserverFunction);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        if (trans.isNewSymbol(term)) {
            Operator op = term.op();
            Matcher m = Pattern.compile("<(.*?)>").matcher(op.name().toString());
            String functionName;
            if (m.find()) {
                functionName = op.name().toString().replace("<" + m.group(1) + ">", "_" + m.group(1))
                        .replace("::", "_").replace("$", "").replace(".", "_");
            } else {
                functionName = op.name().toString().replace("::", "_").replace("$", "").replace(".", "_");
            }
            trans.addKnownSymbol(term, new StringBuilder(functionName));
        }
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, (SortedOperator) term.op(), trans.getKnownSymbol(term).toString());
    }
}
