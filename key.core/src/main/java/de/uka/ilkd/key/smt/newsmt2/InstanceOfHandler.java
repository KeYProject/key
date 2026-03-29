/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

/**
 * This SMT translation handler takes care of instanceof and exactinstanceof functions.
 *
 * @author Jonas Schiffl
 * @author Mattias Ulbrich
 */
public class InstanceOfHandler implements SMTHandler {

    private ParametricFunctionDecl exactInstanceOfOp;
    private ParametricFunctionDecl instanceOfOp;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.instanceOfOp =
            services.getJavaDLTheory().getInstanceofSymbol(services);
        this.exactInstanceOfOp =
            services.getJavaDLTheory().getExactInstanceofSymbol(services);
    }

    @Override
    public boolean canHandle(Operator op) {
        if (op instanceof ParametricFunctionInstance pfi) {
            return exactInstanceOfOp == (pfi.getBase()) || instanceOfOp == (pfi.getBase());
        }
        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        var op = (ParametricFunctionInstance) term.op();
        SExpr inner = trans.translate(term.sub(0), Type.UNIVERSE);
        Sort sort = op.getArgs().head().sort();
        if (exactInstanceOfOp == (op.getBase())) {
            trans.addSort(sort);
            return new SExpr("exactinstanceof", Type.BOOL, inner,
                SExprs.sortExpr(sort));
        } else if (instanceOfOp == (op.getBase())) {
            trans.addSort(sort);
            return SExprs.instanceOf(inner, SExprs.sortExpr(sort));
        } else {
            throw new SMTTranslationException("unexpected case in instanceof-handling: " + term);
        }
    }
}
