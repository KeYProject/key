/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.collection.ImmutableList;

/**
 * this class extends JMenuItem. The objective is to store the Taclet of each item in the item for
 * easier access to the Taclet if the item has been selected
 */
class DefaultTacletMenuItem extends JMenuItem implements TacletMenuItem {

    /**
     *
     */
    private static final long serialVersionUID = -5537139155045230424L;
    private final TacletApp connectedTo;

    /**
     * creates TacletMenuItem attached to a Taclet
     *
     * @param connectedTo the TacletApp that is represented by the item
     * @param notationInfo the NotationInfo used to print terms
     */
    public DefaultTacletMenuItem(TacletApp connectedTo, NotationInfo notationInfo,
            Services services) {
        super(connectedTo.taclet().displayName());
        this.connectedTo = connectedTo;

        SVInstantiations instantiations;
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .getShowUninstantiatedTaclet()) {
            instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        } else {
            instantiations = connectedTo.instantiations();
        }

        SequentViewLogicPrinter tp = SequentViewLogicPrinter.purePrinter(68, notationInfo, services,
            MainWindow.getInstance().getVisibleTermLabels());
        tp.printTaclet(connectedTo.taclet(), instantiations,
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(),
            false);

        int maxTooltipLines =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getMaxTooltipLines();

        // replaced the old code here to fix #1340. (MU)
        String w = tp.result();
        int nlCount = 0;
        int sbl = w.length();
        boolean truncated = false;
        for (int i = 0; i < sbl && !truncated; i++) {
            if (w.charAt(i) == '\n') {
                nlCount += 1;
                if (nlCount > maxTooltipLines) {
                    w = w.substring(0, i);
                    truncated = true;
                }
            }
        }

        StringBuilder taclet_sb = new StringBuilder();
        taclet_sb.append("<html><pre>");
        taclet_sb.append(ascii2html(w));
        taclet_sb.append("</pre>");
        if (truncated) {
            taclet_sb.append("\n<b>!!</b><i> Message has been truncated. "
                + "See View &rarr; ToolTip Options.</i>");
        }

        setToolTipText(taclet_sb.toString());

        // This is a GUI improvement proposed by Stijn: Show the formula
        // you add instead of "Insert hidden"
        // TODO do this not by name but differently ...
        if (getText().equals("insert_hidden")) {
            ImmutableList<TacletGoalTemplate> templates = connectedTo.taclet().goalTemplates();
            if (templates.size() == 1) {
                final LogicPrinter printer = LogicPrinter.purePrinter(new NotationInfo(), services);
                printer.setInstantiation(connectedTo.instantiations());
                printer.printSequent(templates.head().sequent());
                String s = printer.result();
                if (s.length() > 40) {
                    s = s.substring(0, 37) + "...";
                }
                setText(s);
            }
        }

    }

    /**
     * Replaces {@literal <},{@literal >},{@literal &} and new lines with their HTML masks.
     *
     * @param sb The StringBuffer with forbidden HTML characters
     * @return A new StringBuffer with the masked characters.
     */
    protected static StringBuilder ascii2html(String sb) {
        StringBuilder nsb = new StringBuilder();
        String asb = removeEmptyLines(sb);
        int sbl = asb.length();
        for (int i = 0; i < sbl; i++) {
            switch (asb.charAt(i)) {
            case '<':
                nsb.append("&lt;");
                break;
            case '>':
                nsb.append("&gt;");
                break;
            case '&':
                nsb.append("&amp;");
                break;
            case '\n':
                nsb.append("<br>");
                break;
            default:
                nsb.append(asb.charAt(i));
            }
        }
        return nsb;
    }

    private static String removeEmptyLines(String string) {
        // This regular expression matches against lines that only have spaces
        // (' ' or '\t') in them and against trailing new line characters and
        // replaces them with "".
        // This fixes bug #1435, MU
        return string.replaceAll("(?m)^[ \t]*\r?\n|\n$", "");
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.gui.TacletMenuItem#connectedTo()
     */
    @Override
    public TacletApp connectedTo() {
        return connectedTo;
    }

}
