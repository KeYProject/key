/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * This handler is responsible to render number constants Z(3(2(1(#)))) as "123".
 *
 * TODO Should that also do character constants (C) with the same machinery?
 */
public class NumberConstantsHandler implements SMTHandler {

    private Function numberSymbol;
    private Services services;
    private Function negNumberSign;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.services = services;
        numberSymbol = services.getTypeConverter().getIntegerLDT().getNumberSymbol();
        negNumberSign = services.getTypeConverter().getIntegerLDT().getNegativeNumberSign();
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == numberSymbol;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {
        if (term.sub(0).op() == negNumberSign) {
            String s = AbstractTermTransformer.convertToDecimalString(term, services);
            return new SExpr("-", IntegerOpHandler.INT, s.substring(1));
        } else {
            String string = AbstractTermTransformer.convertToDecimalString(term, services);
            return new SExpr(string, IntegerOpHandler.INT);
        }
    }

}
