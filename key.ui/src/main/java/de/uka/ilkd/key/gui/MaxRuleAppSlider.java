/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.awt.Font;
import java.util.Hashtable;
import java.util.LinkedList;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class MaxRuleAppSlider extends JSlider {
    /**
     *
     */
    private static final long serialVersionUID = 5810499328583797609L;
    private static final int MAX_RULE_APPS_LOG10 = 6;
    private static final LinkedList<MaxRuleAppSlider> allInstances =
        new LinkedList<>();
    private final String text;
    private @Nullable KeYMediator mediator;

    /**
     * Create a new slider. A {@code null} mediator is tolerated: the slider stores it in a
     * nullable field and is bound later via {@link #setMediator(KeYMediator)}. The
     * configuration calls below operate on {@code this} while the receiver is still under
     * initialization (EISOP initialization check), and the instance is registered in the
     * shared {@link #allInstances} list before the constructor completes; the effects only
     * take place after construction completes or are deferred into listeners, suppressed
     * with scoped keys.
     *
     * @param mediator the mediator, or {@code null} if not bound yet
     * @param text the label text
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
    public MaxRuleAppSlider(@Nullable KeYMediator mediator, String text) {
        super(HORIZONTAL, 0, MAX_RULE_APPS_LOG10 * 9, 0);
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
            Font labelFont = l.getFont();
            if (labelFont != null) {
                l.setFont(labelFont.deriveFont(9F));
            }
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
            KeYMediator boundMediator = MaxRuleAppSlider.this.mediator;
            if (boundMediator != null) {
                boundMediator.setMaxAutomaticSteps(val);
                setTitle(val);
                updateAllSliders();
            }
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

    /**
     * Binds this slider to a mediator, or unbinds it by passing {@code null}.
     *
     * @param mediator the mediator to bind, or {@code null} to unbind
     */
    public void setMediator(@Nullable KeYMediator mediator) {
        this.mediator = mediator;
    }
}
