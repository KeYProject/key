/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This SMT translation handler takes care of instanceof and exactinstanceof functions.
 *
 * @author Jonas Schiffl
 * @author Mattias Ulbrich
 */
public class InstanceOfHandler implements SMTHandler {

    private SortDependingFunction exactInstanceOfOp;
    private SortDependingFunction instanceOfOp;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.instanceOfOp = Sort.ANY.getInstanceofSymbol(services);
        this.exactInstanceOfOp = Sort.ANY.getExactInstanceofSymbol(services);
    }

    @Override
    public boolean canHandle(Operator op) {
        if (op instanceof SortDependingFunction) {
            SortDependingFunction sdf = (SortDependingFunction) op;
            return exactInstanceOfOp.isSimilar(sdf) || instanceOfOp.isSimilar(sdf);
        }
        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0), Type.UNIVERSE);
        if (exactInstanceOfOp.isSimilar(op)) {
            trans.addSort(op.getSortDependingOn());
            return new SExpr("exactinstanceof", Type.BOOL, inner,
                SExprs.sortExpr(op.getSortDependingOn()));
        } else if (instanceOfOp.isSimilar(op)) {
            trans.addSort(op.getSortDependingOn());
            return SExprs.instanceOf(inner, SExprs.sortExpr(op.getSortDependingOn()));
        } else {
            throw new SMTTranslationException("unexpected case in instanceof-handling: " + term);
        }
    }
}
