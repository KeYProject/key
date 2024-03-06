package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FieldHandler implements IsabelleHandler {
    private final Collection<String> predefinedFields = new HashSet();

    private Sort fieldSort;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets, String[] handlerOptions) throws IOException {
        fieldSort = services.getNamespaces().sorts().lookup("Field");
        predefinedFields.add("created");

        Namespace<Sort> sorts = services.getNamespaces().sorts();
        masterHandler.addPredefinedSort(sorts.lookup(new Name("Field")));
    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof Function && ((Function) op).sort() == fieldSort);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        if (!trans.isKnownSymbol(term)) {
            Operator op = term.op();
            Matcher m = Pattern.compile("<(.*?)>").matcher(op.name().toString());
            assert m.find();
            String fieldName = m.group(1);
            if (predefinedFields.contains(fieldName)) {
                return new StringBuilder(fieldName);
            }
            trans.addKnownSymbol(term, new StringBuilder(fieldName));
        }
        return trans.getKnownSymbol(term);
    }
}
