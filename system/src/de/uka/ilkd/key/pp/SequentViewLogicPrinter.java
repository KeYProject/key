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
 * TermLabel can be retrieved from parameter visibleTermLabels.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SequentViewLogicPrinter extends LogicPrinter {

    /* 
     * Set containing visible TermLabels.
     */
    private final VisibleTermLabels visibleTermLabels;

    public SequentViewLogicPrinter(VisibleTermLabels visibleTermLabels) {
        super();
        this.visibleTermLabels = visibleTermLabels;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Services services,
            VisibleTermLabels visibleTermLabels) {
        super(prgPrinter, notationInfo, services);
        this.visibleTermLabels = visibleTermLabels;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Services services,
            boolean purePrint,
            VisibleTermLabels visibleTermLabels) {
        super(prgPrinter, notationInfo, services, purePrint);
        this.visibleTermLabels = visibleTermLabels;
    }

    public SequentViewLogicPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo,
            Backend backend,
            Services services,
            boolean purePrint,
            VisibleTermLabels visibleTermLabels) {
        super(prgPrinter, notationInfo, backend, services, purePrint);
        this.visibleTermLabels = visibleTermLabels;
    }

    @Override
    protected ImmutableArray<TermLabel> getVisibleLabels(Term t) {

        List<TermLabel> termLabelList = new LinkedList();
        for (TermLabel label : t.getLabels()) {
            if (visibleTermLabels.contains(label)) {
                termLabelList.add(label);
            }
        }

        return new ImmutableArray<TermLabel>(termLabelList);
    }

}
