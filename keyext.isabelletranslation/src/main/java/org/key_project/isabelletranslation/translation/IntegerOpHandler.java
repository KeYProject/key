/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

/**
 * This class handles translation of the integer operators.
 *
 * @author Nils Buchholz
 */
public class IntegerOpHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    private IntegerLDT integerLDT;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets,
            String[] handlerOptions) {
        supportedOperators.clear();
        integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getAdd(), "+");
        supportedOperators.put(integerLDT.getMul(), "*");
        supportedOperators.put(integerLDT.getSub(), "-");
        supportedOperators.put(integerLDT.getDiv(), "euclDiv");
        supportedOperators.put(integerLDT.getMod(), "euclMod");
        supportedOperators.put(integerLDT.getNeg(), "-");

        supportedOperators.put(integerLDT.getJDivision(), "jDiv");
        supportedOperators.put(integerLDT.getJModulo(), "jMod");

        supportedOperators.put(integerLDT.getLessOrEquals(), "<=");
        supportedOperators.put(integerLDT.getLessThan(), "<");
        supportedOperators.put(integerLDT.getGreaterOrEquals(), ">=");
        supportedOperators.put(integerLDT.getGreaterThan(), ">");

        masterHandler.addPreamblesLocales(handlerSnippets);
        masterHandler.addPredefinedSort(integerLDT.targetSort(), "int");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        List<StringBuilder> children = trans.translate(term.subs());
        Operator op = term.op();

        // negation has a special pattern in Isabelle and thus can't be translated like the other
        // functions
        if (op == integerLDT.getNeg()) {
            return new StringBuilder("(-").append(children.get(0)).append(")");
        }

        StringBuilder result = new StringBuilder();
        result.append("((");
        result.append(supportedOperators.get(op));
        result.append(")");
        for (StringBuilder child : children) {
            result.append(" ").append(child);
        }
        result.append(")");
        return result;
    }
}
