/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;

/**
 * This handler is responsible to render number constants Z(3(2(1(#)))) as "123".
 */
public class NumberConstantsHandler implements IsabelleHandler {

    private Function numberSymbol;
    private Services services;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            Properties handlerSnippets,
            String[] handlerOptions) {
        this.services = services;
        numberSymbol = services.getTypeConverter().getIntegerLDT().getNumberSymbol();
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == numberSymbol;
    }

    @Override
    public StringBuilder handle(IsabelleMasterHandler trans, Term term) {
        // TODO This needs an updated AbstractTermTransformer to comply with the new ncore package
        // of KeY
        assert (term instanceof JTerm);

        String string = AbstractTermTransformer
                .convertToDecimalString((JTerm) term, services);
        return new StringBuilder("(").append(string).append("::int)");
    }

}
