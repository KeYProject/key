// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;

import org.antlr.runtime.TokenStream;

@SuppressWarnings("serial")
public class NotDeclException extends KeYSemanticException {

    public NotDeclException(TokenStream input, String cat, String undeclared_symbol, String addtl) {
        super(input, input.getSourceName(), getMessage(cat, undeclared_symbol, addtl));
    }

    public NotDeclException(TokenStream input, String cat, String undeclared_symbol) {
        this(input, cat, undeclared_symbol, "");
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    private static String getMessage(String cat, String undeclaredSymbol, String addtl) {
        return cat + "\n\t" + undeclaredSymbol + "\n" + "not declared "+addtl;
    }

}