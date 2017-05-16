package de.uka.ilkd.key.pp;

import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

public abstract class SearchSequentPrintFilter extends SequentPrintFilter {

    protected String searchString;
    protected boolean regex;
    protected LogicPrinter lp;

    public void setSearchString(String searchString) {
        this.searchString = searchString;
        filterSequent();
    }

    public void setLogicPrinter(SequentViewLogicPrinter logicPrinter) {
        this.lp = logicPrinter;
    }
    
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
        } 
        // This means the search String is not a valid regex (yet!). 
        // Probably because the user is still typing.
        catch (PatternSyntaxException pse) {
            throw new IllegalRegexException(pse);
        } catch (IllegalArgumentException iae) {
            iae.printStackTrace();
        } 
        return p;
    }
    
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