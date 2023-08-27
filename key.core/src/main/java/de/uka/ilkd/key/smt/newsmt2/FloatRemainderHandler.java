/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This handler is a fallback handler that introduces a new uninterpreted function symbol with
 * prefix "uf_" for all FP expressions.
 *
 * This is used in floating point only translation.
 *
 * According declarations are added.
 */
public class FloatRemainderHandler implements SMTHandler {

    public final static String PREFIX = "float_";
    private static final String MAP_KEY = "UNKNOWN_FLOAT_THINGS";

    private Sort floatSort;
    private Sort doubleSort;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        floatSort = services.getTypeConverter().getFloatLDT().targetSort();
        doubleSort = services.getTypeConverter().getDoubleLDT().targetSort();

        masterHandler.getTranslationState().put("float.axioms", "");
        masterHandler.getTranslationState().put("double.axioms", "");
    }

    @Override
    public Capability canHandle(Term term) {
        if (term.sort() == floatSort || term.sort() == doubleSort) {
            return Capability.YES_THIS_INSTANCE;
        }
        return Capability.UNABLE;
    }

    @Override
    public boolean canHandle(Operator op) {
        throw new Error();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {

        Map<Term, SExpr> map = (Map<Term, SExpr>) trans.getTranslationState().get(MAP_KEY);
        if (map == null) {
            map = new HashMap<>();
            trans.getTranslationState().put(MAP_KEY, map);
        }

        SExpr alreadySeen = map.get(term);
        if (alreadySeen != null) {
            return alreadySeen;
        }

        Type type;
        String smtType;
        if (term.sort() == floatSort) {
            type = FloatHandler.FLOAT;
            smtType = "Float32";
        } else {
            type = FloatHandler.DOUBLE;
            smtType = "Float64";
        }

        String name;
        if (term.op() instanceof IProgramVariable) {
            name = PREFIX + term.op();
        } else {
            name = PREFIX + map.size();
        }
        SExpr abbr = new SExpr(name, type);
        SExpr e = new SExpr("declare-const", abbr, new SExpr(smtType));
        trans.addDeclaration(e);
        map.put(term, abbr);
        return abbr;
    }

}
