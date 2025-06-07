/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

/**
 * This handles translation of equals and if-then-else
 */
public class PolymorphicHandler implements IsabelleHandler {

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets,
            String[] handlerOptions) {
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == Equality.EQUALS || op == IfThenElse.IF_THEN_ELSE;
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        Operator op = term.op();
        StringBuilder result;
        if (op == Equality.EQUALS) {
            List<StringBuilder> children = trans.translate(term.subs());
            result = new StringBuilder("(");
            result.append(children.get(0)).append("=").append(children.get(1)).append(")");
            return result;
        }

        if (op == IfThenElse.IF_THEN_ELSE) {
            List<StringBuilder> children = trans.translate(term.subs());
            result = new StringBuilder("(if (");
            result.append(children.get(0)).append(") then ");
            result.append(children.get(1)).append(" else ");
            result.append(children.get(2)).append(")");
            return result;
        }

        throw new Error("unreachable");
    }

}
