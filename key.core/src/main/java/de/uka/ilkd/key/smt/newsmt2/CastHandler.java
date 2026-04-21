/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.smt.SMTTranslationException;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

/**
 * This SMT translation handler takes care of cast expressions <code>T::cast(term)</code>.
 *
 * @author Jonas Schiffl
 * @see CastingFunctionsHandler
 */
public class CastHandler implements SMTHandler {

    private ParametricFunctionDecl anyCast;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) throws IOException {
        this.anyCast = services.getJavaDLTheory().getCastSymbol(services);
        masterHandler.addDeclarationsAndAxioms(handlerSnippets);
    }

    @Override
    public boolean canHandle(Operator op) {
        return op instanceof ParametricFunctionInstance pfi
                && pfi.getBase() == (anyCast);
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        var op = (ParametricFunctionInstance) term.op();
        SExpr inner = trans.translate(term.sub(0));
        Sort depSort = op.getArgs().head().sort();
        trans.addSort(depSort);
        trans.introduceSymbol("cast");
        return SExprs.castExpr(SExprs.sortExpr(depSort), inner);
    }

}
