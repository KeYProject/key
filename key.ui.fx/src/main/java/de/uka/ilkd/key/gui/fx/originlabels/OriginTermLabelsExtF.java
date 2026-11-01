/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.originlabels;

import java.util.List;
import java.util.SortedSet;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.nodeinfo.NodeInfoVisualizerF;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;

/**
 * FX port of the Swing {@code de.uka.ilkd.key.gui.originlabels.OriginTermLabelsExt} — the
 * "Origin Tracking" extension adapter for {@link OriginTermLabel}s and the origin visualizers —
 * as a service-loader provider of the FX extension SPI ({@link KeYGuiExtensionF}). The Swing
 * original (OriginTermLabelsExt.java:31-150, the {@code @KeYGuiExtension.Info} at :36-37)
 * implements {@code KeYGuiExtension.ContextMenu + Tooltip + MainMenu + TermInfo}; this provider
 * ports the same four capabilities:
 * <ul>
 * <li>{@link KeYGuiExtensionF.MainMenuF} — the originlabels View-menu cluster, <em>absorbed</em>
 * from the former direct wiring: the host built it via {@code OriginLabelsF.install(this)} in
 * {@code buildViewMenu} (MainWindowF.java:4275), and the provider now serves the same code path
 * ({@link OriginLabelsF#extensionMenus}) nested under the View menu, so that direct call is
 * superseded and is removed by the host edit (reported by the port). The Swing MainMenu kind
 * holds the "Toggle Term Origin Tracking" checkbox (Swing
 * {@code ToggleTermOriginTrackingAction}, menu path "Origin Tracking",
 * ToggleTermOriginTrackingAction.java:40) plus the "Highlight Origins" toggle
 * (ToggleOriginHighlightAction.java:35, menu path "Origin Tracking" — not ported, see
 * {@link OriginLabelsF}).</li>
 * <li>{@link KeYGuiExtensionF.ContextMenuF} — the Swing-parity context items in exactly the two
 * Swing slots: SEQUENT_VIEW "Show origin" (Swing {@code ShowOriginAction}) and PROOF_TREE one
 * item per open origin visualizer of the clicked node (Swing
 * {@code OpenVisualizerAction}).</li>
 * <li>{@link KeYGuiExtensionF.TooltipF} — the origin tooltip of the hovered term.</li>
 * <li>{@link KeYGuiExtensionF.TermInfoF} — the status-line origin info (the TermInfoF SPI
 * addition of this port; Swing consumes it for {@code MainWindow.setStatusLine}).</li>
 * </ul>
 * <p>
 * Not implemented — {@link KeYGuiExtensionF.StartupF}: there is no startup-driven visualizer
 * initialization outside the SPI to absorb. The registration of the visualizers is
 * constructor-driven ({@code NodeInfoVisualizerF} registers every instance at construction,
 * like the Swing original) and the registry listener is wired by the proof tree view
 * (ProofTreeViewF.java:543-580, mirroring Swing ProofTreeView.java:309) — both keep their
 * behavior unchanged.
 * <p>
 * Toolkit-free instantiation: the provider holds no JavaFX state and every menu item is created
 * inside the getters, which only the running host calls (the lazy-controls pattern of the
 * {@code keyext.caching.fx} {@code CachingExtensionF}), so the service loader may instantiate
 * the provider before any display is up (headless unit tests, verify hooks).
 *
 * @author lanzinger (Swing original), the key.ui.fx team (port)
 */
@NullMarked
@KeYGuiExtensionF.Info(name = "Origin Tracking", optional = true,
    description = "UI support for origin tracking", experimental = false)
public class OriginTermLabelsExtF implements KeYGuiExtensionF, KeYGuiExtensionF.MainMenuF,
        KeYGuiExtensionF.ContextMenuF, KeYGuiExtensionF.TooltipF, KeYGuiExtensionF.TermInfoF {

    // --- MainMenuF -------------------------------------------------

    /**
     * KNOWN-SIMPLIFIED: the Swing original nests its main-menu actions under a NEW top-level
     * menu bar menu "Origin Tracking" — the {@code KeyAction.PATH} "Origin Tracking"
     * (ToggleTermOriginTrackingAction.java:40, ToggleOriginHighlightAction.java:35) is applied
     * by {@code KeYGuiExtensionFacade.addExtensionsToMainMenu} (KeYGuiExtensionFacade.java:
     * 81-89, {@code sortActionIntoMenu}/{@code findMenu} :134-160), which creates a menu bar
     * menu of that name because no built-in menu carries it. This port nests under the
     * built-in View menu instead: the FX View menu hosts the whole originlabels cluster since
     * MP3a (the Swing-parity position of the flat items), and the provider additionally
     * absorbs the View-menu wiring of the Swing <em>direct</em> actions ({@code TermLabelMenu},
     * {@code HidePackagePrefixToggleAction} — not extension contributions in Swing) whose only
     * FX wiring was the {@code OriginLabelsF.install} call the host stops making with this
     * port; a top-level "Origin Tracking" menu would strand them. The contributed menus land
     * at the end of the View menu (the facade appends provider menus after the built-in items).
     */
    @Override
    public String getMenuPath() {
        return "View";
    }

    /**
     * The main-menu contribution (Swing {@code OriginTermLabelsExt.getMainMenuActions},
     * OriginTermLabelsExt.java:63-69): the originlabels View-menu cluster of {@link
     * OriginLabelsF} — the term labels submenu (Swing {@code TermLabelMenu}), the package-prefix
     * toggle (Swing {@code HidePackagePrefixToggleAction}) and the "Origin Tracking" submenu
     * with "Toggle Term Origin Tracking" (Swing {@code ToggleTermOriginTrackingAction}). The
     * cluster is created by {@link OriginLabelsF#extensionMenus} (single-shot, see there), the
     * same installation the legacy direct wiring used.
     */
    @Override
    public List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        return OriginLabelsF.extensionMenus(window);
    }

    // --- ContextMenuF ----------------------------------------------

    /**
     * The sequent context-menu contribution (Swing
     * {@code OriginTermLabelsExt.getContextActions} with {@code ContextMenuKind.SEQUENT_VIEW},
     * OriginTermLabelsExt.java:74-75): the "Show origin" action (Swing
     * {@code ShowOriginAction}, ShowOriginAction.java:35-47) for the clicked position, opening
     * the {@link OriginTermLabelVisualizerF} for it. Swing adds the actions flat into the
     * sequent popup ({@code SequentViewMenu.addExtensionMenu}, SequentViewMenu.java:83-91 — the
     * action's {@code KeyAction.PATH} "View", ShowOriginAction.java:45, is not applied at this
     * site). Enablement: Swing disables the action while
     * {@code TermLabelSettings.useOriginLabels} is off (ShowOriginAction.java:43-44, via a live
     * property listener on the settings) — KNOWN-SIMPLIFIED: the FX popup is rebuilt on every
     * show ({@code SequentTermContextMenuF.build}), so the item carries the build-time state
     * and no listener.
     */
    @Override
    public List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
            PosInSequent pos) {
        MainWindowF window = MainWindowF.getInstance();
        if (window == null) {
            // not started yet (the provider is instantiable without a running toolkit)
            return List.of();
        }
        MenuItem showOrigin = new MenuItem("Show origin");
        showOrigin.setDisable(!ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings()
                .getUseOriginLabels());
        showOrigin.setOnAction(e -> OriginLabelsF.showOrigin(window, pos));
        return List.of(showOrigin);
    }

    /**
     * The proof-tree popup contribution (Swing
     * {@code OriginTermLabelsExt.getContextActions} with {@code ContextMenuKind.PROOF_TREE} and
     * the {@code underlyingObject instanceof Node} check, OriginTermLabelsExt.java:76-79,
     * consumed by {@code ProofTreePopupFactory.create}, ProofTreePopupFactory.java:152-154):
     * one item per open {@link NodeInfoVisualizerF} of the clicked node (Swing
     * {@code NodeInfoVisualizer.getInstances}), text = the visualizer's long name, icon = the
     * Swing {@code IconFactory.WINDOW_ICON} glyph ({@code IconFactoryF.Key.NODE_INFO_WINDOW},
     * both {@code WINDOW_RESTORE}), action = raising the window (Swing
     * {@code OpenVisualizerAction}, OriginTermLabelsExt.java:132-150:
     * {@code MainWindow.getInstance().getSourceViewFrame().toFront(vis)}). Swing sorts these
     * actions by their {@code KeyAction.PATH} "Windows" (OriginTermLabelsExt.java:140) into a
     * sub menu of the popup ({@code sortActionIntoMenu}, KeYGuiExtensionFacade.java:115-132) —
     * mirrored by contributing a {@link Menu} of that name. With no open visualizer nothing is
     * contributed, so the host drops the separator (ProofTreePopupFactory.java:155-157 /
     * {@code ProofTreeViewF#refreshPopupExtensions}).
     */
    @Override
    public List<MenuItem> getProofTreeContextItems(KeYMediatorF mediator, Node node) {
        if (node == null) {
            // the Swing kind check is `underlyingObject instanceof Node`
            // (OriginTermLabelsExt.java:76-77)
            return List.of();
        }
        SortedSet<NodeInfoVisualizerF> visualizers = NodeInfoVisualizerF.getInstances(node);
        if (visualizers.isEmpty()) {
            return List.of();
        }
        Menu windows = new Menu("Windows");
        for (NodeInfoVisualizerF visualizer : visualizers) {
            MenuItem item = new MenuItem(visualizer.getLongName());
            item.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.NODE_INFO_WINDOW));
            item.setOnAction(e -> raiseVisualizer(visualizer));
            windows.getItems().add(item);
        }
        return List.of(windows);
    }

    /**
     * Raises the visualizer window (Swing {@code OpenVisualizerAction.actionPerformed},
     * OriginTermLabelsExt.java:146-149: the Swing visualizers are hosted by the source view
     * frame, {@code SourceViewFrame.toFront(vis)}; the FX visualizers are free
     * {@code Stage}s owned by the main window, so raising is show-when-hidden + {@code
     * toFront}).
     */
    private static void raiseVisualizer(NodeInfoVisualizerF visualizer) {
        if (!visualizer.isShowing()) {
            visualizer.show();
        }
        visualizer.toFront();
    }

    // --- TooltipF ---------------------------------------------------

    /**
     * The sequent-view hover tooltip contribution (Swing
     * {@code OriginTermLabelsExt.getTooltipStrings}, OriginTermLabelsExt.java:98-130, consumed
     * by Swing {@code SequentView.getToolTipText} and the FX
     * {@code SequentViewF#getTooltipText}, SequentViewF.java:1679-1704): the origin of the
     * term and the origins of its (former) sub-terms. KNOWN-SIMPLIFIED: the Swing strings are
     * HTML ("<b>Origin:</b> ...<br>
     * "); the FX hover tooltip is plain text, so the markup is
     * rendered as plain text with line breaks (the same convention as the ported
     * {@code OriginTermLabelVisualizerF}). Like the Swing original a single string is
     * contributed even when it is empty; the FX consumer skips blank strings
     * (SequentViewF.java:1702-1704).
     */
    @Override
    public List<String> getTooltipStrings(KeYMediatorF mediator, PosInSequent pos) {
        if (pos == null || pos.isSequent()) {
            // Swing: no tooltip for the whole-sequent position (OriginTermLabelsExt.java:100-102)
            return List.of();
        }
        Origin origin = OriginTermLabel.getOrigin(pos);
        StringBuilder result = new StringBuilder();
        if (origin != null) {
            result.append("Origin: ").append(origin).append('\n');
        }
        PosInOccurrence pio = pos.getPosInOccurrence();
        OriginTermLabel label = pio == null ? null
                : (OriginTermLabel) ((JTerm) pio.subTerm()).getLabel(OriginTermLabel.NAME);
        if (label != null && !label.getSubtermOrigins().isEmpty()) {
            result.append("Origin of (former) sub-terms:\n");
            for (Origin subOrigin : label.getSubtermOrigins()) {
                result.append(subOrigin).append('\n');
            }
        }
        return List.of(result.toString());
    }

    // --- TermInfoF --------------------------------------------------

    /**
     * The status-line term info contribution (Swing
     * {@code OriginTermLabelsExt.getTermInfoStrings}, OriginTermLabelsExt.java:85-96):
     * "Origin: &lt;origin&gt;" when the position carries an origin ({@code
     * OriginTermLabel.getOrigin(PosInSequent)} is null-safe, OriginTermLabel.java:79-85, and
     * walks up to the next labelled parent term like the Swing original). Swing consumes the
     * strings in {@code SequentViewInputListener} — joined ", "-separated into the status-line
     * text (SequentViewInputListener.java:244-253); the FX host consumption is pending, see
     * {@code KeYGuiExtensionFacadeF.getTermInfoStrings}.
     */
    @Override
    public List<String> getTermInfoStrings(KeYMediatorF mediator, PosInSequent pos) {
        Origin origin = OriginTermLabel.getOrigin(pos);
        if (origin == null) {
            return List.of();
        }
        return List.of("Origin: " + origin);
    }
}
