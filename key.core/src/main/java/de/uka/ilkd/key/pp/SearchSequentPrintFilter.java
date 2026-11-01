/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.pp;

import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This is an interface for filters that are used to modify the sequent view, improving the search
 * function.
 *
 * @author jschiffl
 */
@NullMarked
public abstract class SearchSequentPrintFilter extends SequentPrintFilter {
    private static final Logger LOGGER = LoggerFactory.getLogger(SearchSequentPrintFilter.class);

    /**
     * the String that is to be matched in the sequent view
     */
    @Nullable
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
     * Creates a filter with the given logic printer, which is required by the concrete
     * {@link #filterSequent()} implementations.
     *
     * @param lp the logic printer in use
     */
    protected SearchSequentPrintFilter(LogicPrinter lp) {
        this.lp = lp;
    }

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
     * @param regex indicating whether search string should be treated as regex
     * @return A pattern matching the input String
     * @throws IllegalRegexException if the given pattern is not a valid regex
     */
    public static @Nullable Pattern createPattern(String search, boolean regex)
            throws IllegalRegexException {
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
            LOGGER.warn("Exception compiling pattern", iae);
        }
        return p;
    }

    /**
     * creates a pattern with the current search string and regex option
     * <p>
     * The search string may not be set when the filter is created before any search was entered;
     * the numeric overload throws on that state as it does on a malformed pattern expression (the
     * malformed case is caught here, the {@code null} case propagates exactly as it did before the
     * nullness analysis). Passing the (nullable-typed) search string into the numeric overload is
     * suppressed scoped on this method.
     *
     * @return a brand new shiny pattern
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    protected @Nullable Pattern createPattern() {
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
