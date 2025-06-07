/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;

import org.jetbrains.annotations.NotNull;
import org.jspecify.annotations.NonNull;

/**
 * This class handles the translation of several functions that are already defined in the preamble.
 * This prevents the functions being defined twice.
 * This class also adds the necessary preamble part to the master handler, which is loaded from the
 * "DefinedSymbolsHandler.preamble.xml" file.
 *
 * @see IsabelleMasterHandler
 *
 * @author Nils Buchholz
 */
public class DefinedSymbolsHandler implements IsabelleHandler {
    /**
     * Map of the operators supported by this handler and their respective translation.
     */
    Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {
        masterHandler.addPreamblesLocales(handlerSnippets);
        masterHandler.addPredefinedSort(JavaDLTheory.ANY, "any");

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();

        Namespace<@NonNull Sort> sorts = services.getNamespaces().sorts();
        masterHandler.addPredefinedSort(
            Objects.requireNonNull(sorts.lookup(new Name("java.lang.Object"))),
            "java_lang_Object");
        masterHandler.addPredefinedSort(Objects.requireNonNull(sorts.lookup(new Name("Null"))),
            "Null");
        masterHandler.addPredefinedSort(heapLDT.targetSort(), "Heap");
        masterHandler.addPredefinedSort(locSetLDT.targetSort(), "LocSet");
        masterHandler.addPredefinedSort(seqLDT.targetSort(), "Seq");


        Namespace<@NonNull Function> functionNamespace = services.getNamespaces().functions();
        Map<String, String> definedFunctions = getDefinedFunctions();

        Map<String, String> definedSortDependingFunctions = new HashMap<>();
        definedSortDependingFunctions.put("select", "select");
        definedSortDependingFunctions.put("cast", "cast");
        definedSortDependingFunctions.put("seqGet", "seqGet");

        for (String name : definedFunctions.keySet()) {
            Function function = functionNamespace.lookup(name);
            if (function != null)
                supportedOperators.put(function, definedFunctions.get(name));
        }

        for (Function function : functionNamespace.elements()) {
            if (!(function instanceof SortDependingFunction))
                continue;
            String funName = function.name().toString().split("::")[1];
            for (String name : definedSortDependingFunctions.keySet()) {
                if (funName.equals(name)) {
                    supportedOperators.put(function, definedSortDependingFunctions.get(name));
                }
            }
        }
    }

    /**
     * Returns the list of predefined functions in the preamble.
     *
     * @return The list of predefined functions in the preamble.
     */
    private static @NotNull Map<String, String> getDefinedFunctions() {
        Map<String, String> definedFunctions = new HashMap<>();
        definedFunctions.put("null", "null");
        definedFunctions.put("length", "obj_length");
        definedFunctions.put("arr", "arr");
        definedFunctions.put("wellFormed", "wellFormed");
        definedFunctions.put("anon", "anon");
        definedFunctions.put("store", "store");
        definedFunctions.put("create", "create");

        // Seq functions
        definedFunctions.put("seqLen", "seqLen");
        definedFunctions.put("seqIndexOf", "seqIndexOf");
        definedFunctions.put("seqGetOutside", "seqGetOutside");
        definedFunctions.put("seqEmpty", "seqEmpty");
        definedFunctions.put("seqSingleton", "seqSingleton");
        definedFunctions.put("seqConcat", "seqConcat");
        definedFunctions.put("seqSub", "seqSub");
        definedFunctions.put("seqPerm", "seqPerm");
        definedFunctions.put("seqNPerm", "seqNPerm");
        definedFunctions.put("seqSwap", "seqSwap");
        definedFunctions.put("seqRemove", "seqRemove");
        definedFunctions.put("seqReverse", "seqReverse");


        // LocSet functions
        definedFunctions.put("elementOf", "elementOf");
        definedFunctions.put("subset", "subset");
        definedFunctions.put("disjoint", "disjoint");
        definedFunctions.put("empty", "empty");
        definedFunctions.put("allLocs", "allLocs");
        definedFunctions.put("singleton", "singleton");
        definedFunctions.put("union", "union");
        definedFunctions.put("intersect", "intersect");
        definedFunctions.put("setMinus", "setMinus");
        definedFunctions.put("allFields", "allFields");
        definedFunctions.put("allObjects", "allObjects");
        definedFunctions.put("arrayRange", "arrayRange");
        return definedFunctions;
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        if (term.op() instanceof SortDependingFunction) {
            return SortDependingFunctionHandler.getSortDependingFunctionRef(trans, term,
                (SortDependingFunction) term.op(),
                supportedOperators.get(term.op()));
        }
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, (SortedOperator) term.op(),
            supportedOperators.get(term.op()));
    }
}
