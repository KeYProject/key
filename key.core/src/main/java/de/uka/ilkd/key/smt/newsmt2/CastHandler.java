/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

/**
 * This SMT translation handler takes care of cast expressions <code>T::cast(term)</code>.
 *
 * @author Jonas Schiffl
 * @see CastingFunctionsHandler
 */
public class CastHandler implements SMTHandler {

    private SortDependingFunction anyCast;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) throws IOException {
        this.anyCast = Sort.ANY.getCastSymbol(services);
        masterHandler.addDeclarationsAndAxioms(handlerSnippets);
    }

    @Override
    public boolean canHandle(Operator op) {
        return op instanceof SortDependingFunction
                && ((SortDependingFunction) op).isSimilar(anyCast);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        SExpr inner = trans.translate(term.sub(0));
        Sort depSort = op.getSortDependingOn();
        trans.addSort(depSort);
        trans.introduceSymbol("cast");
        return SExprs.castExpr(SExprs.sortExpr(depSort), inner);
    }

}
