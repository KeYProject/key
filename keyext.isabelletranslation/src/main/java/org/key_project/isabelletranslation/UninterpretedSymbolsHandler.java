/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import org.key_project.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;
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
        masterHandler.addPredefinedSort(JavaDLTheory.ANY, "any");

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();

        Namespace<Sort> sorts = services.getNamespaces().sorts();
        masterHandler.addPredefinedSort(sorts.lookup(new Name("java.lang.Object")), "java_lang_Object");
        masterHandler.addPredefinedSort(sorts.lookup(new Name("Null")), "Null");
        masterHandler.addPredefinedSort(heapLDT.targetSort(), "Heap");
        masterHandler.addPredefinedSort(locSetLDT.targetSort(), "LocSet");
        masterHandler.addPredefinedSort(seqLDT.targetSort(), "Seq");
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
        if (trans.isNewSymbol(term)) {
            String name = PREFIX + op.name().toString();
            trans.addKnownSymbol(term, new StringBuilder(name.replace("::", "_").replace(".", "_")
                    .replace("$", "_").replace("#", "_")));
        }

        String name = trans.getKnownSymbol(term).toString();
        return getFunctionRef(trans, term, op, name);
    }

    static StringBuilder getFunctionRef(IsabelleMasterHandler trans, Term term, SortedOperator op, String name) {
        List<StringBuilder> children = trans.translate(term.subs());
        StringBuilder result = new StringBuilder("(");
        result.append(name);

        for (StringBuilder child : children) {
            result.append(" ").append(child);
        }
        Sort sort = op.sort();
        if (trans.isNewSort(sort)) {
            trans.addGenericSort(sort);
        }
        result.append(")");
        return result;
    }

}