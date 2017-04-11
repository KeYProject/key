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

    protected Pattern createPattern() {
        int searchFlag = 0;
        if (searchString.toLowerCase().equals(searchString)) {
            searchFlag = searchFlag | Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE;
        }

        if (!regex) {
            // search for literal string instead of regExp
            searchFlag = searchFlag | Pattern.LITERAL;
        }

        Pattern p = null;
        try {
            p = Pattern.compile(searchString.replace("\u00A0", "\u0020"), searchFlag);
        } catch (PatternSyntaxException pse) {
            pse.printStackTrace();
        } catch (IllegalArgumentException iae) {
            iae.printStackTrace();
        }
        return p;
    }

}