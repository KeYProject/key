package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.pp.Backend;
import java.util.LinkedList;
import java.util.List;

/**
 * This class optionally hides specific TermLabels. Visibility property of a
 * TermLabel can be retrieved from parameter termLabelPreferences.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SequentViewLogicPrinter extends LogicPrinter {

    /* 
     * Preferences for TermLabel visibility.
     */
    private final TermLabelPreferences termLabelPreferences;

    public SequentViewLogicPrinter(TermLabelPreferences termLabelPreferences) {
        super();
        this.termLabelPreferences = termLabelPreferences;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Services services,
            TermLabelPreferences termLabelPreferences) {
        super(prgPrinter, notationInfo, services);
        this.termLabelPreferences = termLabelPreferences;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Services services,
            boolean purePrint,
            TermLabelPreferences termLabelPreferences) {
        super(prgPrinter, notationInfo, services, purePrint);
        this.termLabelPreferences = termLabelPreferences;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Backend backend,
            Services services,
            boolean purePrint,
            TermLabelPreferences termLabelPreferences) {
        super(prgPrinter, notationInfo, backend, services, purePrint);
        this.termLabelPreferences = termLabelPreferences;
    }

    @Override
    protected ImmutableArray<TermLabel> getLabelsForTerm(Term t) {

        if (termLabelPreferences.hideAllTermLabels()) {
            return new ImmutableArray<TermLabel>();
        }

        List<TermLabel> termLabelList = new LinkedList();
        for (TermLabel label : t.getLabels()) {
            if (termLabelPreferences.isVisible(label)) {
                termLabelList.add(label);
            }
        }

        return new ImmutableArray<TermLabel>(termLabelList);
    }

}
