/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ObserverFunction;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;

/**
 * Handles translation of Observer functions.
 */
public class ObserverFunctionHandler implements IsabelleHandler {
    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {

    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof ObserverFunction);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        if (trans.isNewSymbol(term)) {
            Operator op = term.op();
            Matcher m = Pattern.compile("<(.*?)>").matcher(op.name().toString());
            String functionName;
            if (m.find()) {
                functionName =
                    op.name().toString().replace("<" + m.group(1) + ">", "_" + m.group(1))
                            .replace("::", "_").replace("$", "").replace(".", "_");
            } else {
                functionName =
                    op.name().toString().replace("::", "_").replace("$", "").replace(".", "_");
            }
            trans.addSymbolAndDeclaration(term, new StringBuilder(functionName));
        }
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, (SortedOperator) term.op(),
            trans.getKnownSymbol(term).toString());
    }
}
