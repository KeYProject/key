/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Properties;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

/**
 * Handles translation of parametric functions
 */
public class ParametricFunctionHandler implements IsabelleHandler {

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {

    }

    @Override
    public boolean canHandle(Operator op) {
        return (op instanceof ParametricFunctionInstance);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        assert term.op() instanceof ParametricFunctionInstance;
        var op = (ParametricFunctionInstance) term.op();
        // TODO(DD): Handle more complex parametric functions
        Sort dependentSort = op.getArgs().head().sort();

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

        return getParametricFunctionRef(trans, term, op, name.toString());
    }

    /**
     * Creates a reference to a parametric function
     *
     * @param trans master handler used for translation
     * @param term term the function occurs in
     * @param op the function
     * @param name the name of the function in translation
     * @return reference to a parametric function for use in translation
     */
    static StringBuilder getParametricFunctionRef(IsabelleMasterHandler trans, Term term,
            ParametricFunctionInstance op, String name) {
        StringBuilder ref = new StringBuilder("(").append(name).append("::");
        String parameterTypesDecl =
            op.argSorts().stream().map(trans::translateSortName).collect(Collectors.joining("=>"));
        ref.append(parameterTypesDecl).append("=>").append(trans.translateSortName(op.sort()))
                .append(")");
        return UninterpretedSymbolsHandler.getFunctionRef(trans, term, op, ref.toString());
    }
}
