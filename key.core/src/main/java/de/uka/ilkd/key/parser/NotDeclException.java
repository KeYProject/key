/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

public class NotDeclException extends Exception {
    private static final long serialVersionUID = 1630322840671708203L;

    public NotDeclException(String cat, String undeclared_symbol, String addtl) {
        super(getMessage(cat, undeclared_symbol, addtl));
    }

    public NotDeclException(String cat, String undeclared_symbol) {
        this(cat, undeclared_symbol, "");
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    private static String getMessage(String cat, String undeclaredSymbol, String addtl) {
        return cat + "\n\t" + undeclaredSymbol + "\n" + "not declared " + addtl;
    }

}
