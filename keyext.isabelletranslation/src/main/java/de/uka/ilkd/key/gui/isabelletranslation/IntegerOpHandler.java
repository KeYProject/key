/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

/**
 * This SMT translation handler takes care of integer expressions.
 * <p>
 * This includes the unary and binary integer operations and relational operations.
 *
 * @author Jonas Schiffl
 */
public class IntegerOpHandler implements IsabelleHandler {
    private final Map<Operator, String> supportedOperators = new HashMap<>();

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets,
                     String[] handlerOptions) {
        supportedOperators.clear();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        supportedOperators.put(integerLDT.getAdd(), "+");
        supportedOperators.put(integerLDT.getMul(), "*");
        supportedOperators.put(integerLDT.getSub(), "-");
        supportedOperators.put(integerLDT.getDiv(), "euclDiv");
        supportedOperators.put(integerLDT.getMod(), "euclMod");
        supportedOperators.put(integerLDT.getNeg(), "-");

        supportedOperators.put(integerLDT.getJDivision(), "jdiv");
        supportedOperators.put(integerLDT.getJModulo(), "jmod");

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
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) throws SMTTranslationException {
        List<StringBuilder> children = trans.translate(term.subs());
        Operator op = term.op();

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
