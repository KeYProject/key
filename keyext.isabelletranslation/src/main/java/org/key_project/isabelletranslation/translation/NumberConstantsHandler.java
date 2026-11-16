/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.translation;

import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This handler is responsible to render number constants Z(3(2(1(#)))) as "123".
 */
@NullMarked
public class NumberConstantsHandler implements IsabelleHandler {

    private @Nullable Function numberSymbol;
    private @Nullable Services services;

    @Override
    public void init(IsabelleMasterHandler masterHandler, Services services,
            @Nullable Properties handlerSnippets,
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

        Services theseServices = services;
        if (theseServices == null) {
            throw new NullPointerException("NumberConstantsHandler has not been initialized");
        }

        String string = AbstractTermTransformer
                .convertToDecimalString((JTerm) term, theseServices);
        return new StringBuilder("(").append(string).append("::int)");
    }

}
