package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.pp.Backend;

import java.io.IOException;
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
     * This object is used to determine the TermLabels, which will be printed out.
     */
    private final VisibleTermLabels visibleTermLabels;

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
    protected ImmutableArray<TermLabel> getVisibleTermLabels(Term t) {

        List<TermLabel> termLabelList = new LinkedList<TermLabel>();
        for (TermLabel label : t.getLabels()) {
            if (visibleTermLabels.contains(label)) {
                termLabelList.add(label);
            }
        }

        return new ImmutableArray<TermLabel>(termLabelList);
    }
    
    @Override
    public void printClassName (String className) throws IOException {
        final boolean hidePP = NotationInfo.PRETTY_SYNTAX && NotationInfo.HIDE_PACKAGE_PREFIX;
        if (hidePP) {
            className = className.substring(className.lastIndexOf('.')+1);
        }
        super.printClassName(className);
    }
}
