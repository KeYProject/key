/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLFieldNames;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class handles the translation of field values.
 *
 * @author Nils Buchholz
 */
@NullMarked
public class FieldHandler implements IsabelleHandler {
    /**
     * The predefined fields.
     */
    private final Collection<String> predefinedFields = new HashSet<>();

    /**
     * The Field sort.
     */
    private @Nullable Sort fieldSort;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            @Nullable Properties handlerSnippets, String[] handlerOptions) throws IOException {
        fieldSort = services.getNamespaces().sorts().lookup("Field");
        predefinedFields.add("created");

        Namespace<@NonNull Sort> sorts = services.getNamespaces().sorts();
        Sort fieldSortLookup = sorts.lookup(new Name("Field"));
        if (fieldSortLookup == null) {
            throw new NullPointerException("Sort 'Field' not found in the namespaces");
        }
        masterHandler.addPredefinedSort(fieldSortLookup, "Field");
    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof Function && ((Function) op).sort() == fieldSort && op.arity() == 0);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        if (trans.isNewSymbol(term)) {
            Operator op = term.op();
            Matcher m =
                Pattern.compile(Pattern.quote("" + JavaDLFieldNames.IMPLICIT_NAME_PREFIX) + "(.*?)")
                        .matcher(op.name().toString());
            String fieldName = op.name().toString()
                    .replace(JavaDLFieldNames.IMPLICIT_FIELD_INFIX, "_").replace(".", "_");
            if (m.find()) {
                String captured = m.group(1);
                if (captured != null) {
                    fieldName = captured;
                }
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
