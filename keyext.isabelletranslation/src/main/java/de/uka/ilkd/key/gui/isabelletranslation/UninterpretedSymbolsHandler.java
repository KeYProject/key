/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.util.List;
import java.util.Properties;

/**
 * This handler is a fallback handler that introduces a new uninterpreted function symbol with
 * prefix "u_".
 * <p>
 * According declarations are added.
 */
public class UninterpretedSymbolsHandler implements IsabelleHandler {

    public final static String PREFIX = "var_";

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets,
                     String[] handlerOptions) {
        masterHandler.addPreamblesLocales(handlerSnippets);
        masterHandler.addPredefinedSort(Sort.ANY);

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        Namespace<Sort> sorts = services.getNamespaces().sorts();
        masterHandler.addPredefinedSort(sorts.lookup(new Name("java.lang.Object")));
        masterHandler.addPredefinedSort(sorts.lookup(new Name("Null")));
        masterHandler.addPredefinedSort(heapLDT.targetSort());
        masterHandler.addPredefinedSort(locSetLDT.targetSort());
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
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        SortedOperator op = (SortedOperator) term.op();
        if (!trans.isKnownSymbol(term)) {
            trans.addKnownSymbol(term, new StringBuilder(PREFIX + op.name().toString()));
        }

        String name = trans.getKnownSymbol(term).toString();
        return getFunctionTranslation(trans, term, op, name.replace("::", "_").replace(".", "_"));
    }

    static StringBuilder getFunctionTranslation(IsabelleMasterHandler trans, Term term, SortedOperator op, String name) {
        List<StringBuilder> children = trans.translate(term.subs());
        StringBuilder result = new StringBuilder("(");
        result.append(name);

        for (StringBuilder child : children) {
            result.append(" ").append(child);
        }
        Sort sort = op.sort();
        if (!trans.isKnownSort(sort)) {
            trans.addSort(sort);
        }
        result.append(")");
        return result;
    }

}
