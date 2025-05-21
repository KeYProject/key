/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NonNull;

/**
 * This class handles the translation of field values.
 *
 * @author Nils Buchholz
 */
public class FieldHandler implements IsabelleHandler {
    /**
     * The predefined fields.
     */
    private final Collection<String> predefinedFields = new HashSet<>();

    /**
     * The Field sort.
     */
    private Sort fieldSort;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {
        fieldSort = services.getNamespaces().sorts().lookup("Field");
        predefinedFields.add("created");

        Namespace<@NonNull Sort> sorts = services.getNamespaces().sorts();
        masterHandler.addPredefinedSort(Objects.requireNonNull(sorts.lookup(new Name("Field"))),
            "Field");
    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof Function && ((Function) op).sort() == fieldSort && op.arity() == 0);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
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
            trans.addSymbolAndDeclaration(term, new StringBuilder(fieldName));
            trans.addField((Function) op);
        }
        return trans.getKnownSymbol(term);
    }
}
