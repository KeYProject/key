/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.smt.SMTTranslationException;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

/**
 * This SMT translation handler takes care of those parametric functions f whose return type is
 * coerced, i.e.
 *
 * <pre>
 *     f<[T]>(params) = cast<[T]>(f<[any]>(params))
 * </pre>
 *
 * Currently these are: seqGet and (heap-) select.
 *
 * @author Mattias Ulbrich
 * @see CastHandler
 */
public class CastingFunctionsHandler implements SMTHandler {

    private ParametricFunctionDecl seqGet;
    private ParametricFunctionDecl select;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.seqGet = services.getTypeConverter().getSeqLDT().getSeqGet();
        this.select =
            services.getTypeConverter().getHeapLDT().getSelect();
        masterHandler.addDeclarationsAndAxioms(handlerSnippets);
    }

    @Override
    public boolean canHandle(Operator op) {
        if (op instanceof ParametricFunctionInstance pfi) {
            return seqGet == (pfi.getBase()) || select == (pfi.getBase());
        }
        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        var sdf = (ParametricFunctionInstance) op;
        String name = sdf.getBase().toString();
        String prefixedName = DefinedSymbolsHandler.PREFIX + name;
        trans.introduceSymbol(name);
        SExpr result = trans.handleAsFunctionCall(prefixedName, term);
        Sort dep = sdf.getArgs().head().sort();
        if (dep == JavaDLTheory.ANY) {
            return result;
        } else {
            trans.addSort(dep);
            trans.introduceSymbol("cast");
            return SExprs.castExpr(SExprs.sortExpr(dep), result);
        }
    }
}
