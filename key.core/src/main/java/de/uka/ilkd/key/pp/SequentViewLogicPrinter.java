/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.TermLabelSV;

import org.key_project.util.collection.ImmutableArray;

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

    protected SequentViewLogicPrinter(NotationInfo notationInfo, Services services,
            PosTableLayouter layouter, VisibleTermLabels visibleTermLabels) {
        super(notationInfo, services, layouter);
        this.visibleTermLabels = visibleTermLabels;
    }

    /**
     * Creates a SequentViewLogicPrinter that does not create a position table.
     *
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param services The Services object
     * @param visibleTermLabels the visible term labels
     */
    public static SequentViewLogicPrinter purePrinter(NotationInfo notationInfo, Services services,
            VisibleTermLabels visibleTermLabels) {
        return new SequentViewLogicPrinter(notationInfo, services, PosTableLayouter.pure(),
            visibleTermLabels);
    }

    /**
     * Creates a SequentViewLogicPrinter that does not create a position table.
     *
     * @param lineWidth line width
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param services The Services object
     * @param visibleTermLabels the visible term labels
     */
    public static SequentViewLogicPrinter purePrinter(int lineWidth, NotationInfo notationInfo,
            Services services, VisibleTermLabels visibleTermLabels) {
        return new SequentViewLogicPrinter(notationInfo, services, PosTableLayouter.pure(lineWidth),
            visibleTermLabels);
    }

    /**
     * Creates a SequentViewLogicPrinter that creates a position table.
     *
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param services The Services object
     * @param visibleTermLabels the visible term labels
     */
    public static SequentViewLogicPrinter positionPrinter(NotationInfo notationInfo,
            Services services, VisibleTermLabels visibleTermLabels) {
        return new SequentViewLogicPrinter(notationInfo, services, PosTableLayouter.positionTable(),
            visibleTermLabels);
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
