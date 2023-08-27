/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This handler treats polymorphic symbols, in particular if-then-else and equals.
 *
 * @author Jonas Schiffl
 */
public class PolymorphicHandler implements SMTHandler {

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        // nothing to be done
        // there are also no snippets.
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == Equality.EQUALS || op == IfThenElse.IF_THEN_ELSE;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        if (op == Equality.EQUALS) {
            List<SExpr> children = trans.translate(term.subs());
            children.set(0, SExprs.coerce(children.get(0), Type.UNIVERSE));
            children.set(1, SExprs.coerce(children.get(1), Type.UNIVERSE));
            return new SExpr("=", Type.BOOL, children);
        }

        if (op == IfThenElse.IF_THEN_ELSE) {
            List<SExpr> children = trans.translate(term.subs());
            children.set(0, SExprs.coerce(children.get(0), Type.BOOL));
            children.set(1, SExprs.coerce(children.get(1), Type.UNIVERSE));
            children.set(2, SExprs.coerce(children.get(2), Type.UNIVERSE));
            return new SExpr("ite", Type.UNIVERSE, children);
        }

        throw new Error("unreachable");
    }

}
