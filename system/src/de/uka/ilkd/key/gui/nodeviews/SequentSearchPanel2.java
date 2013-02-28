/**
 * 
 */
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.SearchPanel;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.util.Pair;
import java.awt.Color;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

public class SequentSearchPanel2 extends SearchPanel
{
    
    private final SequentView sequentView;
    private int resultIteratorPos;
    private List<Pair<Integer,Object>> searchResults;
//    private boolean regExpSearch = false;
    public static final Color SEARCH_HIGHLIGHT_COLOR_1 =
            new Color(255, 140, 0, 178);
    public static final Color SEARCH_HIGHLIGHT_COLOR_2 =
            new Color(255, 140, 0, 76);

    public SequentSearchPanel2(SequentView sequentView) {
        this.sequentView = sequentView;
        searchResults = new ArrayList<Pair<Integer,Object>>();
    }

    public void searchPrevious() {
                if (!searchResults.isEmpty()) {
            resetExtraHighlight();
            resultIteratorPos =
                    (resultIteratorPos - 1 + searchResults.size()) %
                    searchResults.size();
            setExtraHighlight(resultIteratorPos);
        }
    }

    public void searchNext() {
        if (!searchResults.isEmpty()) {
            resetExtraHighlight();
            resultIteratorPos = (resultIteratorPos + 1) % searchResults.size();
            setExtraHighlight(resultIteratorPos);
        }
    }
    
    private void setExtraHighlight(int resultIndex) {
        resetHighlight(resultIndex,
                       sequentView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_1));
        sequentView.setCaretPosition(searchResults.get(resultIndex).first);
    }


    private void resetExtraHighlight() {
        resetHighlight(resultIteratorPos,
                       sequentView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_2));
    }
    
    private void resetHighlight(int resultIndex, Object highlight) {
        int pos = searchResults.get(resultIndex).first;
        sequentView.removeHighlight(searchResults.get(resultIndex).second);
        Pair<Integer, Object> highlightPair =
                new Pair<Integer, Object>(pos, highlight);
        sequentView.paintHighlight(new Range(pos, pos + getSearchString().length()), highlight);
        sequentView.updateUpdateHighlights();
        searchResults.set(resultIndex, highlightPair);
    }
    
    private void clearSearchResults() {
        for (Pair result : searchResults) {
            sequentView.removeHighlight(result.second);
        }
        searchResults.clear();
    }
    
    public void search() {
        clearSearchResults();

        if (sequentView == null || sequentView.getText() == null || getSearchString().equals("")) {
            deactivateAllertColor();
            return;
        }

        searchResults.clear();
        resultIteratorPos = 0;

        int searchFlag = 0;
        if (getSearchString().toLowerCase().equals(getSearchString())) {
            // no capital letters used --> case insensitive matching
            searchFlag = searchFlag | Pattern.CASE_INSENSITIVE
                    | Pattern.UNICODE_CASE;
        }
//        if (!regExpSearch) {
//            // search for literal string instead of regExp
//            searchFlag = searchFlag | Pattern.LITERAL;
//        }

        Pattern p;
        try {
            p = Pattern.compile(getSearchString(), searchFlag);
        } catch (PatternSyntaxException pse) {
            activateAllertColor();
            return;
        } catch (IllegalArgumentException iae) {
            activateAllertColor();
            return;
        }
        Matcher m = p.matcher(sequentView.getText());

        boolean loopEnterd = false;
        while (m.find()) {
                int foundAt = m.start();
                Object highlight = sequentView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_2);
                searchResults.add(new Pair<Integer,Object>(foundAt, highlight));
                sequentView.paintHighlight(new Range(foundAt, m.end()), highlight);
                loopEnterd = true;
        }
        if (loopEnterd) {
            sequentView.updateUpdateHighlights();
            deactivateAllertColor();
        } else {
            activateAllertColor();
        }
    }
}