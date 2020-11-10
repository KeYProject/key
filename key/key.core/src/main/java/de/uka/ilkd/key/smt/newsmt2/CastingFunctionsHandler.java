package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.IdentityHashMap;
import java.util.Map;

/**
 * This SMT translation handler takes care of those sort-depending functions f whose return type is
 * coerced, i.e.
 * <pre>
 *     T::f(params) = T::cast(Any::f(params))
 * </pre>
 *
 * Currently these are: seqGet and (heap-) select.
 *
 * @author Mattias Ulbrich
 * @see CastHandler
 */
public class CastingFunctionsHandler implements SMTHandler {

    private Services services;
    private SortDependingFunction seqGet;
    private SortDependingFunction select;

    @Override
    public void init(MasterHandler masterHandler, Services services) {
        this.services = services;
        this.seqGet = services.getTypeConverter().getSeqLDT().getSeqGet(Sort.ANY, services);
        this.select = services.getTypeConverter().getHeapLDT().getSelect(Sort.ANY, services);
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        if (op instanceof SortDependingFunction) {
            SortDependingFunction sdf = (SortDependingFunction) op;
            return seqGet.isSimilar(sdf) || select.isSimilar(sdf);
        }
        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        SortDependingFunction sdf = (SortDependingFunction) op;
        String name = sdf.getKind().toString();
        String prefixedName = DefinedSymbolsHandler.PREFIX + name;
        trans.addFromSnippets(name);
        SExpr result = trans.handleAsFunctionCall(prefixedName, term);
        Sort dep = sdf.getSortDependingOn();
        if (dep == Sort.ANY) {
            return result;
        } else {
            return SExprs.castExpr(SExprs.sortExpr(dep), result);
        }
    }
}
