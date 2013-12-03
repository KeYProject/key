package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;
import java.util.HashSet;
import java.util.Set;
import javax.swing.JCheckBoxMenuItem;

/**
 * This class is used by SequentViewLogicPrinter to determine which TermLabels
 * are printed and which are not.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class HiddenTermLabels {

    private final JCheckBoxMenuItem hideAllCheckBox;
    private final Set<Name> hiddenTermLabels;

    public boolean allHidden() {
        return hideAllCheckBox.isSelected();
    }

    public HiddenTermLabels(JCheckBoxMenuItem hideAllCheckBox) {
        this.hideAllCheckBox = hideAllCheckBox;
        this.hiddenTermLabels = new HashSet();
    }

    public boolean contains(TermLabel label) {
        return hiddenTermLabels.contains(label.name());
    }

    public boolean contains(Name name) {
        return allHidden() || hiddenTermLabels.contains(name);
    }

    public void add(Name name) {
        hiddenTermLabels.add(name);
    }

    public void remove(Name name) {
        hiddenTermLabels.remove(name);
    }

}
