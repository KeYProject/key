/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This simple SMT translation handler takes care of logical variables.
 *
 * It merely adds "var_" in front of the variable name.
 *
 * For integer variables the SMTLib type is set to Int.
 *
 * @author Jonas Schiffl
 */
public class LogicalVariableHandler implements SMTHandler {

    static final String VAR_PREFIX = "var_";

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        // nothing to be done
    }

    @Override
    public boolean canHandle(Operator op) {
        return op instanceof LogicVariable;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {
        return makeVarRef(term.toString(), term.sort());
    }

    public static SExpr makeVarDecl(String name, Sort sort) {
        if (sort.name().equals(IntegerLDT.NAME)) {
            // Special casing integer quantification: Avoid conversion to "U".
            // Caution: Must be in sync with quantifier treatment.
            return new SExpr(VAR_PREFIX + name, new SExpr("Int"));
        } else {
            return new SExpr(VAR_PREFIX + name, new SExpr("U"));
        }
    }

    public static SExpr makeVarRef(String name, Sort sort) {
        if (sort.name().equals(IntegerLDT.NAME)) {
            // Special casing integer quantification: Avoid conversion to "U".
            // Caution: Must be in sync with quantifier treatment.
            return new SExpr(VAR_PREFIX + name, IntegerOpHandler.INT);
        } else {
            return new SExpr(VAR_PREFIX + name, Type.UNIVERSE);
        }
    }
}
