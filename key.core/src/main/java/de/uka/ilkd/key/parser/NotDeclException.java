package de.uka.ilkd.key.parser;

import org.antlr.runtime.TokenStream;

public class NotDeclException extends KeYSemanticException {
    private static final long serialVersionUID = 1630322840671708203L;

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
        return cat + "\n\t" + undeclaredSymbol + "\n" + "not declared " + addtl;
    }

}
