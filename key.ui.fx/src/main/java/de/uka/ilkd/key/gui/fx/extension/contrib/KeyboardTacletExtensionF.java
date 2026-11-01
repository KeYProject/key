/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.Tab;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.proof.Node;

import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * JavaFX port of the keyboard-taclet extension, counter-part of the Swing
 * {@code de.uka.ilkd.key.gui.KeyboardTacletExtension}
 * (key.ui/src/main/java/de/uka/ilkd/key/gui/KeyboardTacletExtension.java:51-85). The extension
 * contributes the "Active Taclets" west-drawer tab ({@link KeyboardTacletPanelF}) that lets the
 * user apply taclets via the keyboard: a prefix of the rule name selects the taclet, number keys
 * pick one of its applications and a unique match is applied directly in direct mode.
 * <p>
 * The {@link KeYGuiExtensionF.Info} mirrors the Swing annotation exactly
 * (KeyboardTacletExtension.java:57-59): name "Keyboard Taclet Control", {@code optional = true},
 * and {@code experimental} keeps the Swing default {@code true} (the FX annotation mirrors the
 * Swing default at KeYGuiExtension.java:88).
 * <p>
 * KNOWN-SIMPLIFIED decisions of this port (each marked at the respective site):
 * <ul>
 * <li>The Swing provider registers the {@code KeYSelectionListener} inside
 * {@code getPanels} (KeyboardTacletExtension.java:66-71, before the panel is even created, the
 * listener closes over the panel field); the FX provider registers it in the {@link #init}
 * startup hook — the host calls {@code getLeftPanelTabs} while building the drawer hosts
 * (MainWindowF.buildDrawerHosts) and {@code init} afterwards, so the listener registration moves
 * to the dedicated lifecycle hook. Selection events may fire from the prover thread, so the
 * panel update is marshalled with {@link FxUtil#runLater}.</li>
 * <li>The Swing {@code TabPanel} has no tab icon; the FX tab carries the
 * {@link IconFactoryF.Key#KEYBOARD_TACLET} drawer-identity glyph (see the established drawer
 * icon convention of the other west-drawer items).</li>
 * <li>The dock-title {@code CDropDownButton} "Options" with the four check-style toggles
 * (KeyboardTacletExtension.java:199-209) is surfaced as the panel header check boxes plus the
 * {@link KeyboardTacletPanelF#getTitleActions()} check-style title-action hook; rendering the
 * check flavour in the tab context menu ({@code DockWorkspace.createTabContextMenu}) is host
 * work (see the KNOWN-SIMPLIFIED ledger).</li>
 * </ul>
 */
@NullMarked
@KeYGuiExtensionF.Info(name = "Keyboard Taclet Control",
    description = "This extension control over the application of taclets via the keyboard.",
    optional = true)
public class KeyboardTacletExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.LeftPanelF,
        KeYGuiExtensionF.StartupF {

    /** the lazily-built "Active Taclets" panel (west-drawer tab). */
    private @Nullable KeyboardTacletPanelF panel;

    /** the window and mediator of the running app; wired in {@link #init}, nullable in tests. */
    private @Nullable MainWindowF window;
    private @Nullable KeYMediatorF mediator;

    @Override
    public List<Tab> getLeftPanelTabs(@Nullable MainWindowF window,
            @Nullable KeYMediatorF mediator) {
        if (window != null) {
            this.window = window;
        }
        if (mediator != null) {
            this.mediator = mediator;
        }
        // MP10: the host registers extension left-panel tabs as west-drawer items
        // (MainWindowF.buildDrawerHosts), exactly one tab like the Swing singleton panel
        // (KeyboardTacletExtension.java:82-83)
        KeyboardTacletPanelF p = getPanel();
        Tab tab = new Tab(p.getTitle(), p);
        // the tab graphic becomes the west drawer toggle button's icon; the Swing TabPanel has
        // no tab icon, the keyboard glyph follows the drawer-identity convention
        tab.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.KEYBOARD_TACLET));
        tab.setClosable(false);
        return List.of(tab);
    }

    private KeyboardTacletPanelF getPanel() {
        // lazy singleton: the panel constructs FX controls, so the provider must stay
        // instantiable without a running FX toolkit (unit tests); getLeftPanelTabs is called
        // repeatedly by the MainWindowF verify hooks — the singleton keeps one tab identity
        if (panel == null) {
            panel = new KeyboardTacletPanelF(window, mediator);
        }
        return panel;
    }

    @Override
    public void init(@Nullable MainWindowF window, @Nullable KeYMediatorF mediator) {
        if (window != null) {
            this.window = window;
        }
        if (mediator == null) {
            // startup hook without a mediator (headless runs): nothing to wire
            return;
        }
        this.mediator = mediator;
        KeyboardTacletPanelF p = getPanel();
        // the host builds the drawer hosts during window construction, before this init hook —
        // re-seed the panel with the real window/mediator references (the hover listener of the
        // Swing panel, KeyboardTacletExtension.java:143-149, is attached by the wire exactly
        // once)
        p.wire(window, mediator);
        // Swing: the KeYSelectionListener is registered in getPanels
        // (KeyboardTacletExtension.java:66-71): selectedNodeChanged → panel.setGoal(goal)
        mediator.getSelectionModel().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                // selection events may fire from the prover thread → marshal to the FX thread
                FxUtil.runLater(() -> {
                    KeyboardTacletPanelF pnl = panel;
                    if (pnl != null) {
                        pnl.setGoal(mediator.getSelectedGoal());
                    }
                });
            }
        });
    }
}
