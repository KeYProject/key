/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.api;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.util.List;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tab;
import javafx.scene.input.KeyCombination;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.jspecify.annotations.NullMarked;

/**
 * The FX-native GUI-extension SPI, counter-part of {@code de.uka.ilkd.key.gui.extension.api.
 * KeYGuiExtension} of the Swing module {@code key.ui} (KeYGuiExtension.java:31-308). Every FX
 * extension implements this marker interface and is registered in the service-loader file
 * <code>META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF</code>, then
 * implements one or more of the nested capability interfaces below.
 * <p>
 * The capabilities mirror the Swing set with JavaFX-typed surfaces ({@link Menu}s instead of
 * {@code JMenu}s, {@link Control}s instead of {@code JComponent}s, {@link Tab}s instead of the
 * Swing {@code TabPanel}). The host ({@link MainWindowF}) discovers the providers through
 * {@link de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF} and integrates them into the
 * menu bar, toolbars, status bar, docking layout, settings dialog and sequent context menu —
 * exactly the slots the Swing {@code KeYGuiExtensionFacade} fills in {@code key.ui}.
 *
 * @author Alexander Weigl
 * @author MP9.0 extension SPI port (FX)
 */
@NullMarked
public interface KeYGuiExtensionF {
    /**
     * Describes the annotated extension (Swing {@code KeYGuiExtension.Info},
     * KeYGuiExtension.java:46-89).
     */
    @Retention(RetentionPolicy.RUNTIME)
    @interface Info {
        /**
         * Simple name of this extension, else the fqdn of the class is used.
         *
         * @return non-null string
         */
        String name() default "";

        /**
         * Long description of this extension (what does it do? who developed it?).
         *
         * @return a string, default empty
         */
        String description() default "";

        /**
         * Optional extensions can be disabled by the user (Swing semantics).
         *
         * @return a boolean
         */
        boolean optional() default false;

        /**
         * Marks an extension as experimental. Swing only loads experimental extensions with the
         * {@code --experimental} command-line flag; the FX port reserves the flag semantics and
         * defaults to {@code true} like the Swing original (KeYGuiExtension.java:88).
         *
         * @return a boolean
         */
        boolean experimental() default true;

        /**
         * Loading priority of this extension; baseline is zero (Swing
         * KeYGuiExtension.java:80).
         *
         * @return the priority
         */
        int priority() default 0;
    }

    /**
     * Main-menu extension: contributes whole {@link Menu} objects that the host appends to the
     * menu bar as new separate menus (Swing {@code KeYGuiExtension.MainMenu},
     * KeYGuiExtension.java:92-107 — the Swing original contributes actions that the facade
     * groups into one "Extensions" {@code JMenu}, MainWindow.createMenuBar :983; the FX SPI
     * keeps the grouping decision with the extension and contributes ready {@code Menu}s).
     * The five built-in menus (File / Proof / View / Options / About) and their item sets are
     * never touched.
     * <p>
     * P4 (B13): a provider may return a non-empty {@link #getMenuPath()} to nest its menus
     * into the menu bar instead of appending them on the top level — the mirror of the Swing
     * {@code KeyAction.PATH} dot-separated path (KeyAction.java:46, applied by
     * {@code KeYGuiExtensionFacade.sortActionIntoMenu}), matching menu names by text and
     * creating missing menus along the way.
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of menus
     */
    interface MainMenuF {
        List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator);

        /**
         * The dot-separated menu path under which the contributed menus are nested (Swing
         * {@code KeyAction.PATH}, KeyAction.java:39-46). The empty path keeps the FX default:
         * the menus are appended as new separate top-level menus after the built-in About menu.
         * A non-empty path (e.g. {@code "View.Tools"}) matches or creates a top-level menu of
         * the first segment in the existing menu bar, then descends/creates the nested sub
         * menus, and finally splices the contributed menu items into the innermost menu.
         *
         * @return the path, may be empty
         */
        default String getMenuPath() {
            return "";
        }
    }

    /**
     * Toolbar extension: contributes {@link Control}s that the host appends into an extra
     * toolbar next to the built-in file/proof toolbars (Swing
     * {@code KeYGuiExtension.Toolbar}, KeYGuiExtension.java:170-183).
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of controls
     */
    interface ToolbarF {
        List<Control> getToolbarControls(MainWindowF window, KeYMediatorF mediator);
    }

    /**
     * Status-line extension: contributes {@link Control}s that the host appends to the status
     * bar (Swing {@code KeYGuiExtension.StatusLine}, KeYGuiExtension.java:203-214).
     *
     * @return non-null, emptiable list of controls
     */
    interface StatusLineF {
        List<Control> getStatusLineControls();
    }

    /**
     * Left-panel extension: contributes {@link Tab}s that the host registers as dockables in
     * the left docking area (Swing {@code KeYGuiExtension.LeftPanel},
     * KeYGuiExtension.java:127-143 — the Swing original returns {@code TabPanel}s for the left
     * JTabbedPane).
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of tabs
     */
    interface LeftPanelF {
        List<Tab> getLeftPanelTabs(MainWindowF window, KeYMediatorF mediator);
    }

    /**
     * Context-menu extension for the sequent term menu and (P4, C24) the proof-tree popup
     * (Swing {@code KeYGuiExtension.ContextMenu}, KeYGuiExtension.java:145-168 — the two
     * {@code ContextMenuKind} slots {@code SEQUENT_VIEW} and {@code PROOF_TREE}). The host
     * renders the sequent items inside the "Extensions" section of the sequent context menu,
     * and the proof-tree items after a separator at the end of the proof-tree popup
     * (Swing {@code ProofTreePopupFactory}, ProofTreePopupFactory.java:152-154).
     *
     * @param mediator the mediator of the window
     * @param goal the goal whose sequent was clicked
     * @param pos the clicked position
     * @return non-null, emptiable list of menu items
     */
    interface ContextMenuF {
        List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
                PosInSequent pos);

        /**
         * The menu items contributed to the proof-tree popup for the given node (Swing
         * {@code KeYGuiExtensionFacade.addContextMenuItems} with
         * {@code ContextMenuKind.PROOF_TREE}, ProofTreePopupFactory.java:152-154). The empty
         * list is the default — most extensions only serve the sequent slot.
         *
         * @param mediator the mediator of the window
         * @param node the clicked proof-tree node
         * @return non-null, emptiable list of menu items
         */
        default List<MenuItem> getProofTreeContextItems(KeYMediatorF mediator, Node node) {
            return List.of();
        }
    }

    /**
     * Settings extension: contributes a {@link SettingsProviderF} into the settings dialog
     * (Swing {@code KeYGuiExtension.Settings}, KeYGuiExtension.java:216-227).
     *
     * @return non-null settings provider
     */
    interface SettingsF {
        SettingsProviderF getSettings();
    }

    /**
     * Sequent-view tooltip extension: contributes term-information strings for the given
     * position (Swing {@code KeYGuiExtension.Tooltip}, KeYGuiExtension.java:186-201, shown by
     * Swing {@code SequentView.getToolTipText}). P4 (D30): the FX sequent view appends the
     * strings to its hover tooltip (SequentViewF#getTooltipText).
     *
     * @param mediator the mediator of the window
     * @param pos the position of the term whose info shall be shown
     * @return non-null, emptiable list of strings
     */
    interface TooltipF {
        List<String> getTooltipStrings(KeYMediatorF mediator, PosInSequent pos);
    }

    /**
     * Keyboard-shortcut extension: contributes additional shortcuts bound to a host view
     * (Swing {@code KeYGuiExtension.KeyboardShortcuts}, KeYGuiExtension.java:234-248, bound
     * into the Swing input maps by {@code KeYGuiExtensionFacade.installKeyboardShortcuts} for
     * the sequent view, goal list, proof tree, strategy selection, source view and info view).
     * P4 (D36): the FX host binds {@link ShortcutF}s as key-pressed event filters on the view
     * node whose <em>componentId</em> matches, see
     * {@code KeYGuiExtensionFacadeF.installKeyboardShortcuts}.
     */
    interface KeyboardShortcutsF {

        /** The sequent view (Swing {@code KeyboardShortcuts.SEQUENT_VIEW}). */
        String SEQUENT_VIEW = "SEQUENT_VIEW";
        /** The goal list (Swing {@code KeyboardShortcuts.GOAL_LIST}). */
        String GOAL_LIST = "GOAL_LIST";
        /** The proof tree (Swing {@code KeyboardShortcuts.PROOF_TREE_VIEW}). */
        String PROOF_TREE_VIEW = "PROOF_TREE_VIEW";
        /**
         * The strategy-selection view (Swing {@code KeyboardShortcuts.STRATEGY_SELECTION_VIEW}).
         */
        String STRATEGY_SELECTION_VIEW = "STRATEGY_SELECTION_VIEW";
        /** The source view (Swing {@code KeyboardShortcuts.SOURCE_VIEW}). */
        String SOURCE_VIEW = "SOURCE_VIEW";
        /** The info view (Swing {@code KeyboardShortcuts.INFO_TREE}). */
        String INFO_TREE = "INFO_TREE";

        /**
         * The shortcuts to bind for the given view.
         *
         * @param mediator the mediator of the window
         * @param componentId one of the component constants above
         * @return non-null, emptiable list of shortcuts
         */
        default List<ShortcutF> getShortcuts(KeYMediatorF mediator, String componentId) {
            return List.of();
        }

        /**
         * One view-scoped shortcut: a {@link KeyCombination} with the action to run when it is
         * pressed while the view it is bound to has the keyboard focus.
         */
        record ShortcutF(String componentId, KeyCombination combination, Runnable action) {
            public ShortcutF {
                java.util.Objects.requireNonNull(componentId);
                java.util.Objects.requireNonNull(combination);
                java.util.Objects.requireNonNull(action);
            }
        }
    }

    /**
     * Startup extension: the host calls {@link #init(MainWindowF, KeYMediatorF)} once at
     * startup, after discovery, before layout-dependent interaction (Swing
     * {@code KeYGuiExtension.Startup}, KeYGuiExtension.java:109-125).
     */
    interface StartupF {
        /**
         * Initialization hook, called once at the end of the app startup after the discovery.
         * Can be used to register listeners and initialize controls.
         *
         * @param window the main window
         * @param mediator the mediator of the window
         */
        default void init(MainWindowF window, KeYMediatorF mediator) {
        }
    }
}
