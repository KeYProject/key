/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package key.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.util.List;
import java.util.Properties;

/**
 * This handler treats polymorphic symbols, in particular if-then-else and equals.
 *
 * @author Jonas Schiffl
 */
public class PolymorphicHandler implements IsabelleHandler {

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets,
                     String[] handlerOptions) {
        // nothing to be done
        // there are also no snippets.
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == Equality.EQUALS || op == IfThenElse.IF_THEN_ELSE;
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
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
