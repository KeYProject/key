/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LogicVariable;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

/**
 * Handles the translation of LogicVariables.
 */
public class LogicalVariableHandler implements IsabelleHandler {

    static final String VAR_POSTFIX = UninterpretedSymbolsHandler.POSTFIX;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) {

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

    /**
     * Used to reference a given variable in the translation.
     *
     * @param trans The master handler used for translation
     * @param name intended name of the variable
     * @param sort sort of the variable
     * @return reference of the given variable in the translation
     */
    public static StringBuilder makeVarRef(IsabelleMasterHandler trans, String name, Sort sort) {
        StringBuilder result = new StringBuilder("(");
        result.append(name).append(VAR_POSTFIX).append("::").append(trans.translateSortName(sort))
                .append(")");
        return result;
    }
}
