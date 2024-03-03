/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;

import java.util.Properties;

/**
 * This handler is responsible to render number constants Z(3(2(1(#)))) as "123".
 * <p>
 * TODO Should that also do character constants (C) with the same machinery?
 */
public class NumberConstantsHandler implements IsabelleHandler {

    private Function numberSymbol;
    private Services services;
    private Function negNumberSign;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets,
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
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        String string = AbstractTermTransformer.convertToDecimalString(term, services);
        return new StringBuilder("(").append(string).append("::int)");
    }

}
