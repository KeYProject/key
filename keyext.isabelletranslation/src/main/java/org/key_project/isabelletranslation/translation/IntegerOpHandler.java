/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.translation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class handles translation of the integer operators.
 *
 * @author Nils Buchholz
 */
@NullMarked
public class IntegerOpHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    private @Nullable IntegerLDT integerLDT;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            @Nullable Properties handlerSnippets,
            String[] handlerOptions) {
        supportedOperators.clear();
        IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();
        if (ldt == null) {
            throw new NullPointerException("No IntegerLDT found in the services");
        }
        integerLDT = ldt;

        supportedOperators.put(ldt.getAdd(), "+");
        supportedOperators.put(ldt.getMul(), "*");
        supportedOperators.put(ldt.getSub(), "-");
        supportedOperators.put(ldt.getDiv(), "euclDiv");
        supportedOperators.put(ldt.getMod(), "euclMod");
        supportedOperators.put(ldt.getNeg(), "-");

        supportedOperators.put(ldt.getJDivision(), "jDiv");
        supportedOperators.put(ldt.getJModulo(), "jMod");

        supportedOperators.put(ldt.getLessOrEquals(), "<=");
        supportedOperators.put(ldt.getLessThan(), "<");
        supportedOperators.put(ldt.getGreaterOrEquals(), ">=");
        supportedOperators.put(ldt.getGreaterThan(), ">");

        // the handlerSnippets are null if no preamble snippets file exists; without them the
        // preamble cannot be constructed, mirroring the previous NPE on entrySet()
        // (crash-equivalent)
        if (handlerSnippets == null) {
            throw new NullPointerException("No preamble snippets for IntegerOpHandler");
        }
        masterHandler.addPreamblesLocales(handlerSnippets);
        masterHandler.addPredefinedSort(ldt.targetSort(), "int");
    }

    @Override
    public boolean canHandle(Operator op) {
        return supportedOperators.containsKey(op);
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        List<StringBuilder> children = trans.translate(term.subs());
        Operator op = term.op();

        IntegerLDT ldt = integerLDT;
        if (ldt == null) {
            throw new NullPointerException("IntegerOpHandler has not been initialized");
        }

        // negation has a special pattern in Isabelle and thus can't be translated like the other
        // functions
        if (op == ldt.getNeg()) {
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
