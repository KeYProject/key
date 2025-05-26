/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;

import org.jspecify.annotations.NonNull;

/**
 * This class handles translation of the instance and exactInstance function.
 *
 * @author Nils Buchholz
 */
public class InstanceOperatorHandler implements IsabelleHandler {
    /**
     * Map of the operators supported by this handler and their respective translation.
     */
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets, String[] handlerOptions) throws IOException {
        Namespace<@NonNull Function> functionNamespace = services.getNamespaces().functions();
        Map<String, String> definedSortDependingFunctions = new HashMap<>();

        definedSortDependingFunctions.put("instance", "instanceof");
        definedSortDependingFunctions.put("exactInstance", "exactInstance");

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

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        SortDependingFunction op = (SortDependingFunction) term.op();
        String functionName = supportedOperators.get(op);
        String dependingSortTypeName = trans.translateSortName(op.getSortDependingOn()) + "_type";

        StringBuilder result = new StringBuilder("(");
        result.append("(").append(functionName).append(") ");
        result.append(trans.translate(term.sub(0))).append(" ");
        result.append(dependingSortTypeName).append(")");

        return result;
    }
}
