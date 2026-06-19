/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;

/**
 * This handles translation of quantifiers.
 */
public class QuantifierHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {
        supportedOperators.put(Quantifier.ALL, "\\<forall>");
        supportedOperators.put(Quantifier.EX, "\\<exists>");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        StringBuilder result = makeBoundedVarRef(trans, term, supportedOperators.get(term.op()));
        result.append(". (");
        result.append(trans.translate(term.sub(0))).append("))");
        return result;
    }

    /**
     * Makes a reference to a binding variable and the variables it binds
     *
     * @param trans master handler used for translation
     * @param term the term in which the binding variable occurs
     * @param name name of the binding variable in translation
     * @return a reference to a binding variable and the variables it binds
     */
    public static StringBuilder makeBoundedVarRef(IsabelleMasterHandler trans, Term term,
            String name) {
        StringBuilder result = new StringBuilder("(");
        result.append(name);
        for (QuantifiableVariable bv : term.boundVars()) {
            Sort sort = bv.sort();
            result.append(" ")
                    .append(LogicalVariableHandler.makeVarRef(trans, bv.name().toString(), sort));
            if (trans.isNewSort(sort)) {
                trans.addGenericSort(sort);
            }
        }
        return result;
    }

}
