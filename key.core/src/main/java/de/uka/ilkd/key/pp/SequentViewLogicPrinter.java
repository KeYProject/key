package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.util.pp.StringBackend;
import org.key_project.util.collection.ImmutableArray;

import java.util.LinkedList;
import java.util.List;

/**
 * Subclass of {@link LogicPrinter} used in GUI. Any GUI-specific code for pretty-printing should be
 * put in here, so that code of {@link LogicPrinter} stays independent of GUI as much as possible.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SequentViewLogicPrinter extends LogicPrinter {

    /*
     * This object is used to determine the TermLabels, which will be printed out.
     */
    private final VisibleTermLabels visibleTermLabels;

    public SequentViewLogicPrinter(NotationInfo notationInfo,
            Services services, VisibleTermLabels visibleTermLabels) {
        super(notationInfo, services);
        this.visibleTermLabels = visibleTermLabels;
    }

    public SequentViewLogicPrinter(NotationInfo notationInfo,
            Services services, boolean purePrint, VisibleTermLabels visibleTermLabels) {
        super(notationInfo, services, purePrint);
        this.visibleTermLabels = visibleTermLabels;
    }

    public SequentViewLogicPrinter(int lineWidth, NotationInfo notationInfo, Services services,
            boolean purePrint, VisibleTermLabels visibleTermLabels) {
        super(notationInfo, services, purePrint, lineWidth);
        this.visibleTermLabels = visibleTermLabels;
    }

    @Override
    protected ImmutableArray<TermLabel> getVisibleTermLabels(Term t) {

        List<TermLabel> termLabelList = new LinkedList<>();
        if (visibleTermLabels != null) {
            for (TermLabel label : t.getLabels()) {
                if (label instanceof TermLabelSV || visibleTermLabels.contains(label)) {
                    termLabelList.add(label);
                }
            }
        }

        return new ImmutableArray<>(termLabelList);
    }

    @Override
    public void printClassName(String className) {
        final boolean hidePP =
            notationInfo.isPrettySyntax() && getNotationInfo().isHidePackagePrefix();
        if (hidePP) {
            className = className.substring(className.lastIndexOf('.') + 1);
        }
        super.printClassName(className);
    }
}
