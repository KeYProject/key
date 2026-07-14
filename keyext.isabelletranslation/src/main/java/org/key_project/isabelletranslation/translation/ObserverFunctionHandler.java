/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLFieldNames;
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
            String opName = term.op().name().toString();
            Matcher m = Pattern
                    .compile(Pattern.quote("" + JavaDLFieldNames.IMPLICIT_NAME_PREFIX) + "(.*?)")
                    .matcher(opName);
            String functionName;
            if (m.find()) {
                functionName =
                    opName.replace(JavaDLFieldNames.IMPLICIT_NAME_PREFIX + m.group(1),
                        "_" + m.group(1))
                            .replace(JavaDLFieldNames.SEPARATOR, "_")
                            .replace(JavaDLFieldNames.IMPLICIT_NAME_PREFIX + "", "")
                            .replace(".", "_");
            } else {
                functionName =
                    opName.replace(JavaDLFieldNames.SEPARATOR, "_")
                            .replace(JavaDLFieldNames.FIELD_PREFIX + "", "")
                            .replace(".", "_");
            }
            trans.addSymbolAndDeclaration(term, new StringBuilder(functionName));
        }
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, (SortedOperator) term.op(),
            trans.getKnownSymbol(term).toString());
    }
}
