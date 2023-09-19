/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.BOOL;
import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.UNIVERSE;

/**
 * This handler is a fallback handler that introduces a new uninterpreted function symbol with
 * prefix "u_".
 *
 * According declarations are added.
 */
public class UninterpretedSymbolsHandler implements SMTHandler {

    public final static String PREFIX = "u_";

    // TODO This flag does not seem to be 100% what it is supposed to. Refactor. MU
    private boolean enableQuantifiers;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        enableQuantifiers = !HandlerUtil.NO_QUANTIFIERS.get(services);
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
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortedOperator op = (SortedOperator) term.op();
        String name = PREFIX + op.name().toString();
        if (!trans.isKnownSymbol(name)) {
            trans.addDeclaration(HandlerUtil.funDeclaration(op, name));
            if (op.sort() != Sort.FORMULA && (enableQuantifiers || op.arity() == 0)) {
                trans.addAxiom(HandlerUtil.funTypeAxiom(op, name, trans));
            }
            trans.addKnownSymbol(name);
        }

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        SExpr.Type exprType = term.sort() == Sort.FORMULA ? BOOL : UNIVERSE;
        return new SExpr(name, exprType, children);
    }

}
