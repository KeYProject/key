/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.Hashtable;
import java.util.LinkedList;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;

public class MaxRuleAppSlider extends JSlider {
    /**
     *
     */
    private static final long serialVersionUID = 5810499328583797609L;
    private static final int MAX_RULE_APPS_LOG10 = 6;
    private static final LinkedList<MaxRuleAppSlider> allInstances =
        new LinkedList<>();
    private final String text;
    private KeYMediator mediator;

    public MaxRuleAppSlider(KeYMediator mediator, String text) {
        super(SwingConstants.HORIZONTAL, 0, MAX_RULE_APPS_LOG10 * 9, 0);
        this.text = text;

        this.mediator = mediator;

        // set up slider labels
        Hashtable<Integer, JLabel> labelTable = new Hashtable<>();

        for (int n = 0; n <= MAX_RULE_APPS_LOG10; n++) {
            int val = (int) Math.pow(10, n);
            String sval =
                String.valueOf(
                    val >= 10000 ? val >= 1000000 ? (val / 1000000) + "M" : (val / 1000) + "k"
                            : +val);
            JLabel l = new JLabel(sval);
            l.setFont(l.getFont().deriveFont(9F));
            labelTable.put(n * 9, l);
        }

        setLabelTable(labelTable);
        setPaintLabels(true);

        // show ticks
        setMajorTickSpacing(9);
        setMinorTickSpacing(1);
        setPaintTicks(true);

        // add change listener
        addChangeListener(e -> {
            int val = getPos();
            MaxRuleAppSlider.this.mediator.setMaxAutomaticSteps(val);
            setTitle(val);
            updateAllSliders();
        });

        setTitle(0);

        allInstances.add(this);
    }

    public int getPos() {
        int n = getValue();
        int major = n / 9;
        int minor = n % 9;
        int val = (minor + 1) * (int) Math.pow(10, major);
        return val;
    }

    public void setPos(int maxRuleApps) {
        if (maxRuleApps > 0) {
            int major = (int) (Math.log(maxRuleApps) / Math.log(10));
            int minor = maxRuleApps / (int) Math.pow(10, major) - 1;
            int initPos = Math.max(0, Math.min(MAX_RULE_APPS_LOG10 * 9, major * 9 + minor));
            setValue(initPos);
        }
    }

    private void setTitle(int maxRuleApps) {
        setBorder(BorderFactory.createTitledBorder(text + ": " + maxRuleApps));
    }

    public void refresh() {
        if (mediator != null) {
            final int steps = mediator.getMaxAutomaticSteps();
            setPos(steps);
            setTitle(steps);
        }
    }

    private void updateAllSliders() {
        for (MaxRuleAppSlider allInstance : allInstances) {
            allInstance.refresh();
        }
    }

    public void setMediator(KeYMediator mediator) {
        this.mediator = mediator;
    }
}
