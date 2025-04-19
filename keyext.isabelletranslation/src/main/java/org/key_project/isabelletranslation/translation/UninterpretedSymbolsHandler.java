/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;

/**
 * This handler is a fallback handler that introduces a new uninterpreted function symbol with
 * prefix in subscript
 * <p>
 * According declarations are added.
 */
public class UninterpretedSymbolsHandler implements IsabelleHandler {

    public final static String POSTFIX = "\\<^sub>v\\<^sub>a\\<^sub>r";

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets,
            String[] handlerOptions) {
    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof Function && !bindsVars(op)) || op instanceof ProgramVariable;
    }

    /*
     * return true if op binds in at least one argument.
     */
    private static boolean bindsVars(Operator op) {
        for (int i = 0; i < op.arity(); i++) {
            if (op.bindVarsAt(i)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        SortedOperator op = (SortedOperator) term.op();
        if (trans.isNewSymbol(term)) {
            String name = op.name() + POSTFIX;
            trans.addSymbolAndDeclaration(term,
                new StringBuilder(name.replace("::", "_").replace(".", "_")
                        .replace("$", "_").replace("#", "_")));
        }

        String name = trans.getKnownSymbol(term).toString();
        return getFunctionRef(trans, term, op, name);
    }

    /**
     * Creates a reference to a function for use in translations.
     *
     * @param trans master handler used for translation
     * @param term the term the function occurs in as the top operator
     * @param op the function
     * @param name name of the function in translations
     * @return a reference to a function for use in translations.
     */
    static StringBuilder getFunctionRef(IsabelleMasterHandler trans, Term term, SortedOperator op,
            String name) {
        List<StringBuilder> children = trans.translate(term.subs());
        StringBuilder result = new StringBuilder("(");
        result.append(name);

        for (StringBuilder child : children) {
            result.append(" ").append(child);
        }
        Sort sort = op.sort();
        if (trans.isNewSort(sort)) {
            trans.addGenericSort(sort);
        }
        result.append(")");
        return result;
    }

}
