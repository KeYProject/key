package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;
import java.util.HashSet;
import java.util.Set;

/**
 * This class is used by SequentViewLogicPrinter to determine which TermLabels are printed
 * and which are not.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class TermLabelPreferences {

    private final Set<Name> hiddenTermLabels;

    public abstract boolean hideAllTermLabels();

    public TermLabelPreferences() {
        hiddenTermLabels = new HashSet();
    }
    
    public boolean isVisible(TermLabel label) {
        return isVisible(label.name());
    }

    public boolean isVisible(Name name) {
        return !hideAllTermLabels() && !hiddenTermLabels.contains(name);
    }

    public void hideTermLabel(Name name) {
        hiddenTermLabels.add(name);
    }

    public void unhideTermLabel(Name name) {
        hiddenTermLabels.add(name);
    }
}
