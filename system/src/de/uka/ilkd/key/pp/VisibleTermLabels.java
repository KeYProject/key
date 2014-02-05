package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * This abstract class is used by SequentViewLogicPrinter to determine the set
 * of printed TermLabels.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class VisibleTermLabels {

    public boolean contains(TermLabel label) {
        return contains(label.name());
    }

    public abstract boolean contains(Name name);

}
