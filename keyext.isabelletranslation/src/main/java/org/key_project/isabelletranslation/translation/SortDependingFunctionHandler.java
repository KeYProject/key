/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Properties;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

/**
 * Handles translation of sort depending functions
 */
public class SortDependingFunctionHandler implements IsabelleHandler {

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {

    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof SortDependingFunction);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        assert term.op() instanceof SortDependingFunction;
        SortDependingFunction op = (SortDependingFunction) term.op();
        Sort dependentSort = op.getSortDependingOn();

        if (trans.isNewSort(dependentSort)) {
            trans.addGenericSort(dependentSort);
        }
        StringBuilder name;
        if (trans.isNewSymbol(term)) {
            name = LogicalVariableHandler.makeVarRef(trans, op.name().toString().split("::")[1],
                dependentSort);
            trans.addSymbolAndDeclaration(term, name);
        } else {
            name = trans.getKnownSymbol(term);
        }

        return getSortDependingFunctionRef(trans, term, op, name.toString());
    }

    /**
     * Creates a reference to a sort depending function
     *
     * @param trans master handler used for translation
     * @param term term the function occurs in
     * @param op the function
     * @param name the name of the function in translation
     * @return reference to a sort depending function for use in translation
     */
    static StringBuilder getSortDependingFunctionRef(IsabelleMasterHandler trans, Term term,
            SortDependingFunction op, String name) {
        StringBuilder ref = new StringBuilder("(").append(name).append("::");
        String parameterTypesDecl =
            op.argSorts().stream().map(trans::translateSortName).collect(Collectors.joining("=>"));
        ref.append(parameterTypesDecl).append("=>").append(trans.translateSortName(op.sort()))
                .append(")");
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, op, ref.toString());
    }
}
