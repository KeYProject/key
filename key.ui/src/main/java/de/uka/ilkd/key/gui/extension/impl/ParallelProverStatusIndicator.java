/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.awt.Dimension;
import java.awt.FontMetrics;
import java.awt.Insets;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Status-line indicator showing the active prover mode: {@code SC} for the single-core (legacy)
 * prover, or {@code MT N×} for the multi-core prover with {@code N} worker threads. Left-clicking
 * it
 * switches between the two modes; right-clicking offers a menu to pick the worker count.
 *
 * <p>
 * It reads and writes the same {@link GeneralSettings#PARALLEL_PROVER_ENABLED} setting as the
 * preference pane and reacts to its change events, so the whole UI stays consistent however the
 * mode is changed.
 *
 * @author Claude (KeY multithreading effort)
 */
@KeYGuiExtension.Info(experimental = false, name = "Prover Mode in Status Line", optional = false,
    description = "Shows and toggles the single-core / multi-core prover mode in the status line.")
public class ParallelProverStatusIndicator
        implements KeYGuiExtension, KeYGuiExtension.StatusLine, KeYGuiExtension.Startup {

    private final JButton button = new JButton();

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        button.setFocusable(false);
        button.addActionListener(e -> toggleMode());
        button.addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                maybeShowMenu(e);
            }

            @Override
            public void mouseReleased(MouseEvent e) {
                maybeShowMenu(e);
            }
        });
        generalSettings().addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_ENABLED,
            evt -> refresh());
        generalSettings().addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_THREADS,
            evt -> refresh());
        fixSize();
        refresh();
    }

    private static GeneralSettings generalSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
    }

    private static int cores() {
        return Math.max(1, Runtime.getRuntime().availableProcessors());
    }

    /**
     * Keep the button a constant size regardless of whether {@code SC} or {@code MT N×} is shown,
     * by
     * sizing it for the widest possible label.
     */
    private void fixSize() {
        FontMetrics fm = button.getFontMetrics(button.getFont());
        Insets in = button.getInsets();
        int w = fm.stringWidth("MT " + cores() + "x") + in.left + in.right + 12;
        int h = fm.getHeight() + in.top + in.bottom + 4;
        Dimension d = new Dimension(w, h);
        button.setPreferredSize(d);
        button.setMinimumSize(d);
        button.setMaximumSize(d);
    }

    private void toggleMode() {
        generalSettings().setParallelProverEnabled(!generalSettings().isParallelProverEnabled());
    }

    private void maybeShowMenu(MouseEvent e) {
        if (!e.isPopupTrigger()) {
            return;
        }
        GeneralSettings gs = generalSettings();
        JPopupMenu menu = new JPopupMenu();

        JRadioButtonMenuItem single = new JRadioButtonMenuItem("Single-core");
        single.setSelected(!gs.isParallelProverEnabled());
        single.addActionListener(a -> gs.setParallelProverEnabled(false));
        menu.add(single);
        menu.addSeparator();

        // Offer a small, sensible set of worker counts capped at the available processors.
        TreeSet<Integer> counts = new TreeSet<>(List.of(2, 4, 8, cores()));
        for (Integer n : new ArrayList<>(counts)) {
            if (n < 2 || n > cores()) {
                continue;
            }
            JRadioButtonMenuItem item = new JRadioButtonMenuItem("Multi-core, " + n + " workers");
            item.setSelected(gs.isParallelProverEnabled()
                    && effectiveThreads(gs) == n);
            item.addActionListener(a -> {
                gs.setParallelProverThreadCount(n);
                gs.setParallelProverEnabled(true);
            });
            menu.add(item);
        }
        menu.show(button, e.getX(), e.getY());
    }

    private static int effectiveThreads(GeneralSettings gs) {
        return Math.max(1, Math.min(gs.getParallelProverThreadCount(), cores()));
    }

    private void refresh() {
        GeneralSettings gs = generalSettings();
        if (gs.isParallelProverEnabled()) {
            int threads = effectiveThreads(gs);
            button.setText("MT " + threads + "x");
            button.setToolTipText("Multi-core prover active (" + threads
                + " workers). Left-click for single-core; right-click to choose the worker count.");
        } else {
            button.setText("SC");
            button.setToolTipText("Single-core prover active. Left-click for multi-core; "
                + "right-click to choose the worker count.");
        }
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        // A leading strut adds a bit of space between this indicator and its neighbours.
        return List.of((JComponent) Box.createHorizontalStrut(8), button);
    }
}
