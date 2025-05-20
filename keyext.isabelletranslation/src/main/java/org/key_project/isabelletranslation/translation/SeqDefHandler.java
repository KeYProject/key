/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

/**
 * Handles translation of seqDef function.
 */
public class SeqDefHandler implements IsabelleHandler {

    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {
        supportedOperators.put(services.getTypeConverter().getSeqLDT().getSeqDef(), "SeqDef");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        StringBuilder arg1 = trans.translate(term.sub(0));
        StringBuilder arg2 = trans.translate(term.sub(1));
        String arg3 = "(\\<lambda>"
            + LogicalVariableHandler.makeVarRef(trans, term.boundVars().get(0).name().toString(),
                term.boundVars().get(0).sort())
            + ". " +
            " to_any (" + trans.translate(term.sub(2)) + "))";

        return new StringBuilder("(seqDef ").append(arg1).append(arg2).append(arg3).append(")");
    }
}
