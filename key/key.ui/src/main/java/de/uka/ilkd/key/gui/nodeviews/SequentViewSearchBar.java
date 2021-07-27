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

package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.SearchBar;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.util.Pair;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;



/*
 * Search bar implementing search function for SequentView.
 */

public class SequentViewSearchBar extends SearchBar {

    private static final long serialVersionUID = 9102464983776181771L;
    public static final ColorSettings.ColorProperty SEARCH_HIGHLIGHT_COLOR_1 =
            ColorSettings.define("[sequentSearchBar]highlight_1", "",
                    new Color(0, 140, 255, 178));

    public static final ColorSettings.ColorProperty SEARCH_HIGHLIGHT_COLOR_2 =
            ColorSettings.define("[sequentSearchBar]highlight_2", "",
                    new Color(0, 140, 255, 100));

    public static enum SearchMode {
        HIGHLIGHT("Highlight", IconFactory.SEARCH_HIGHLIGHT.get(16)),
        HIDE("Hide", IconFactory.SEARCH_HIDE.get(16)),
        REGROUP("Regroup", IconFactory.SEARCH_REGROUP.get(16));
        private String displayName;
        public final Icon icon;

        private SearchMode(String name, Icon icon) {
            this.displayName = name;
            this.icon = icon;
        }

        @Override
        public String toString() {
            return this.displayName;
        }
    }

    private final List<Pair<Integer, Object>> searchResults;
    private int resultIteratorPos;
    private SequentView sequentView;
    private JCheckBox regExpCheckBox;
    private JComboBox<SearchMode> searchModeBox;

    public SequentViewSearchBar(SequentView sequentView) {
        this.sequentView = sequentView;
        searchResults = new ArrayList<Pair<Integer, Object>>();
    }

    public void setSequentView(SequentView sequentView) {
        if(this.sequentView != sequentView) {
            sequentView.setFilter(this.sequentView.getFilter()); 
        }
        this.sequentView = sequentView;
        search();
    }

    public SequentView getSequentView() {
        return this.sequentView;
    }

    public void setSearchMode(SearchMode mode) {
        searchModeBox.setSelectedItem(mode);
    }

    @Override
    public void createUI() {
        super.createUI();
        regExpCheckBox = new JCheckBox("RegExp", false);
        regExpCheckBox.setName("toggleRegExpSearch");
        regExpCheckBox.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                searchField.requestFocus();
                if (sequentView.getFilter() instanceof SearchSequentPrintFilter) {
                    ((SearchSequentPrintFilter) sequentView.getFilter()).setRegex(regExpCheckBox.isSelected());
                }
                search();
            }
        });
        regExpCheckBox.setToolTipText("Evaluate as regular expression");
        add(regExpCheckBox);

        searchModeBox = new JComboBox<SearchMode>(SearchMode.values());
        searchModeBox.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                if (e.getStateChange() == ItemEvent.SELECTED) {
                    switch ((SearchMode) searchModeBox.getSelectedItem()) {
                    case HIDE:
                        sequentView.setFilter(new HideSequentPrintFilter(sequentView.getLogicPrinter(), regExpCheckBox.isSelected()));
                        search();
                        break;
                    case REGROUP:
                        sequentView.setFilter(new RegroupSequentPrintFilter(sequentView.getLogicPrinter(), regExpCheckBox.isSelected()));
                        search();
                        break;
                    case HIGHLIGHT:
                        sequentView.setFilter(new IdentitySequentPrintFilter());
                        search();
                        break;
                    default:
                        sequentView.setFilter(new IdentitySequentPrintFilter());
                        break;
                    }
                }
            }
        });
        searchModeBox.setToolTipText("<html>Determines search behaviour: <b>" + SearchMode.HIDE.displayName
                + "</b> only shows sequent formulas that match the search. <b>" + SearchMode.REGROUP.displayName
                + "</b> arranges the matching formulas around the sequence arrow. <b>"
                + SearchMode.HIGHLIGHT.displayName + "</b> leaves the sequent unchanged.</html>");
        add(searchModeBox);
    }

    @Override
    public void searchNext() {
        if (!searchResults.isEmpty()) {
            resetExtraHighlight();
            resultIteratorPos++;
            resultIteratorPos %= searchResults.size();
            setExtraHighlight(resultIteratorPos);
        }
    }

    @Override
    public void searchPrevious() {
        if (!searchResults.isEmpty()) {
            resetExtraHighlight();
            // Adding the size to avoid -1 underflow (bugfix, MU)
            resultIteratorPos += searchResults.size() - 1;
            resultIteratorPos %= searchResults.size();
            setExtraHighlight(resultIteratorPos);
        }
    }

    @Override
    public void setVisible(boolean vis) {
        super.setVisible(vis);
        if (sequentView != null) {
            if (vis) {
                search();
            } else {
                clearSearchResults();
                searchModeBox.setSelectedIndex(0);
            }
        }
    }

    /**
     * searches for the occurrence of the specified string
     */
    @Override
    public boolean search(String search) {
        clearSearchResults();

        if (sequentView.getFilter() instanceof SearchSequentPrintFilter) {
            SearchSequentPrintFilter searchSequentPrintFilter = (SearchSequentPrintFilter) sequentView.getFilter();
            searchSequentPrintFilter.setLogicPrinter(sequentView.getLogicPrinter());
            searchSequentPrintFilter.setSearchString(searchField.getText());
        }

        sequentView.printSequent();

        if (sequentView == null || sequentView.getText() == null || search.equals("") || !this.isVisible()) {
            return true;
        }

        resultIteratorPos = 0;
        Pattern p;
        
        try {
            p = SearchSequentPrintFilter.createPattern(search, regExpCheckBox.isSelected());
            searchField.setToolTipText("");
        } catch (IllegalRegexException pse) {
            searchField.setToolTipText("Not a valid regular expression!");
            return false;
        }

        if (p == null) return false;

        Matcher m = p.matcher(sequentView.getText().replace("\u00A0", "\u0020"));

        boolean loopEnterd = false;
        while (m.find()) {
            int foundAt = m.start();
            Object highlight = sequentView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_2.get());
            searchResults.add(new Pair<Integer, Object>(foundAt, highlight));
            sequentView.paintHighlight(new Range(foundAt, m.end()), highlight);
            loopEnterd = true;
        }
        return loopEnterd;
    }

    /**
    * searches for the given string and displays the search-bar.
    * @param searchTerm string to search for. If regex is enabled, the string will be escaped
    */
    public void searchFor(String searchTerm) {
        if (regExpCheckBox.isSelected()) {
            // https://stackoverflow.com/questions/60160/how-to-escape-text-for-regular-expression-in-java
            String escaped = searchTerm.replaceAll("[-\\[\\]{}()*+?.,\\\\\\\\^$|#\\\\s]", "\\\\$0");
            searchField.setText(escaped);
        } else {
            searchField.setText(searchTerm);
        }
        setVisible(true);
        search();
    }

    private void setExtraHighlight(int resultIndex) {
        resetHighlight(resultIndex, sequentView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_1.get()));
        sequentView.setCaretPosition(searchResults.get(resultIndex).first);
    }

    private void resetExtraHighlight() {
        resetHighlight(resultIteratorPos, sequentView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_2.get()));
    }

    private void resetHighlight(int resultIndex, Object highlight) {
        int pos = searchResults.get(resultIndex).first;
        sequentView.removeHighlight(searchResults.get(resultIndex).second);
        Pair<Integer, Object> highlightPair = new Pair<>(pos, highlight);
        sequentView.paintHighlight(new Range(pos, pos + searchField.getText().length()), highlight);
        searchResults.set(resultIndex, highlightPair);
    }

    private void clearSearchResults() {
        for (Pair<Integer, Object> result : searchResults) {
            sequentView.removeHighlight(result.second);
        }
        searchResults.clear();
    }
}