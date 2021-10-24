package de.uka.ilkd.key.smt.newsmt2;

import org.hamcrest.core.SubstringMatcher;

/**
 * To check whether a string occurs in another string ...
 * but with potentially different spacing.
 *
 * @author Mattias Ulbrich
 */
class ContainsModuloSpaces extends SubstringMatcher {
    public ContainsModuloSpaces(String string) {
        super(string);
    }

    @Override
    protected boolean evalSubstringOf(String string) {
        String needle = substring.replaceAll("\\s+", " ");
        String haystack = string.replaceAll("\\s+", " ");
        return haystack.contains(needle);
    }

    @Override
    protected String relationship() {
        return "containing (modulo spaces)";
    }
}
