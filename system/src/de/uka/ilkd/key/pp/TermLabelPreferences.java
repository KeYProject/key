package de.uka.ilkd.key.pp;

import java.util.Set;
import java.util.TreeSet;

/**
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 * This class is used by LogicPrinter to determine which TermLabels are printed
 * and which are not. If not otherwise set, LogicPrinter will use the return
 * value of function TermLabelPreferences.getDefaults().
 */
public abstract class TermLabelPreferences {

    public final Set<String> hiddenTermLabels = new TreeSet();

    public abstract boolean hideAllTermLabels();

    public static TermLabelPreferences getDefaults() {
        return new TermLabelPreferences() {
            @Override
            public boolean hideAllTermLabels() {
                return false;
            }
        };
    }
}
