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
 * TermLabel can be retrieved from parameter hiddenTermLabels.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SequentViewLogicPrinter extends LogicPrinter {

    /* 
     * Set containing hidden TermLabels.
     */
    private final HiddenTermLabels hiddenTermLabels;

    public SequentViewLogicPrinter(HiddenTermLabels hiddenTermLabels) {
        super();
        this.hiddenTermLabels = hiddenTermLabels;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Services services,
            HiddenTermLabels hiddenTermLabels) {
        super(prgPrinter, notationInfo, services);
        this.hiddenTermLabels = hiddenTermLabels;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Services services,
            boolean purePrint,
            HiddenTermLabels hiddenTermLabels) {
        super(prgPrinter, notationInfo, services, purePrint);
        this.hiddenTermLabels = hiddenTermLabels;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Backend backend,
            Services services,
            boolean purePrint,
            HiddenTermLabels hiddenTermLabels) {
        super(prgPrinter, notationInfo, backend, services, purePrint);
        this.hiddenTermLabels = hiddenTermLabels;
    }

    @Override
    protected ImmutableArray<TermLabel> getLabelsForTerm(Term t) {

        if (hiddenTermLabels.allHidden()) {
            return new ImmutableArray<TermLabel>();
        }

        List<TermLabel> termLabelList = new LinkedList();
        for (TermLabel label : t.getLabels()) {
            if (!hiddenTermLabels.contains(label)) {
                termLabelList.add(label);
            }
        }

        return new ImmutableArray<TermLabel>(termLabelList);
    }

}
