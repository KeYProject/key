package org.key_project.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import org.key_project.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FieldHandler implements IsabelleHandler {
    private final Collection<String> predefinedFields = new HashSet<>();

    private Sort fieldSort;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        fieldSort = services.getNamespaces().sorts().lookup("Field");
        predefinedFields.add("created");

        Namespace<Sort> sorts = services.getNamespaces().sorts();
        masterHandler.addPredefinedSort(sorts.lookup(new Name("Field")), "Field");
    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof Function && ((Function) op).sort() == fieldSort && op.arity() == 0);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        if (trans.isNewSymbol(term)) {
            Operator op = term.op();
            Matcher m = Pattern.compile("<(.*?)>").matcher(op.name().toString());
            String fieldName = op.name().toString().replace("::$", "_").replace(".", "_");
            if (m.find()) {
                fieldName = m.group(1);
            }
            if (predefinedFields.contains(fieldName)) {
                return new StringBuilder(fieldName);
            }
            trans.addKnownSymbol(term, new StringBuilder(fieldName));
            trans.addField((Function) op);
        }
        return trans.getKnownSymbol(term);
    }
}
