package de.uka.ilkd.key.pp;

import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

/**
 * This is an interface for filters that are used to
 * modify the sequent view, improving the search function.
 *
 * @author jschiffl
 */
public abstract class SearchSequentPrintFilter extends SequentPrintFilter {

    /**
     * the String that is to be matched in the sequent view
     */
    String searchString;

    /**
     * the logic printer in use
     */
    LogicPrinter lp;

    /**
     * indicating whether the user input should be treated as regular expression
     */
    boolean regex;

    /**
     * sets the filter's search string
     *
     * @param searchString the new search string
     */
    public void setSearchString(String searchString) {
        this.searchString = searchString;
        antec = null;
        succ = null;
        filterSequent();
    }

    public void setLogicPrinter(SequentViewLogicPrinter logicPrinter) {
        this.lp = logicPrinter;
    }

    /**
     * @param search the String we are looking for
     * @param regex  indicating whether search string should be treated as regex
     * @return A pattern matching the input String
     * @throws IllegalRegexException if the given pattern is not a valid regex
     */
    public static Pattern createPattern(String search, boolean regex) throws IllegalRegexException {
        int searchFlag = 0;
        if (search.toLowerCase().equals(search)) {
            searchFlag = searchFlag | Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE;
        }

        // (DS) We replace non-breaking space ("&nbsp;", \\u00a0)
        // by ordinary space (\\u0020).
        // This became necessary due to the change to HTML Documents
        // in the course of the introduction of syntax highlighting.

        // (JS) Replace special characters with escaped special
        // characters and contract several whitespaces into a
        // single one so that line breaks are treated correctly.

        if (!regex) {
            search = search.replaceAll("[^\\s\\u00a0\\w]", "\\\\$0");
        }

        Pattern p = null;
        try {
            String s = search.replaceAll("[\\s\\u00a0]+", "\\\\s+");
            p = Pattern.compile(s, searchFlag);
        } catch (PatternSyntaxException pse) {
            throw new IllegalRegexException(pse); // not a valid regex (yet?)
        } catch (IllegalArgumentException iae) {
            iae.printStackTrace();
        }
        return p;
    }

    /**
     * creates a pattern with the current search string and regex option
     * @return a brand new shiny pattern
     */
    protected Pattern createPattern() {
        try {
            return createPattern(this.searchString, this.regex);
        } catch (IllegalRegexException e) {
            return null;
        }
    }

    public void setRegex(boolean selected) {
        this.regex = selected;
    }
}