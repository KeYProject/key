package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * This abstract class is used by SequentViewLogicPrinter to determine the set of printed
 * TermLabels.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public interface VisibleTermLabels {
    public boolean contains(TermLabel label);

    public abstract boolean contains(Name name);
}
