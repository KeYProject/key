/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class handles the translation of the bounded sum function.
 *
 * @author Nils Buchholz
 */
@NullMarked
public class BSumHandler implements IsabelleHandler {
    /**
     * Map of the operators supported by this handler and their respective translation.
     */
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            @Nullable Properties handlerSnippets, String[] handlerOptions) throws IOException {
        supportedOperators.clear();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getBsum(), "\\<Sum>");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        String name = supportedOperators.get(term.op());
        if (name == null) {
            throw new NullPointerException("No translation registered for operator "
                + term.op().name());
        }
        StringBuilder result = QuantifierHandler.makeBoundedVarRef(trans, term, name);
        result.append("=");
        result.append(trans.translate(term.sub(0))).append("..<")
                .append(trans.translate(term.sub(1))).append(". ");
        result.append(trans.translate(term.sub(2))).append(")");
        return result;
    }
}
