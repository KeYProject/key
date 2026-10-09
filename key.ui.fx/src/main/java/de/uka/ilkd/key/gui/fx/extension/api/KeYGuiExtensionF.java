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

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;

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
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of menus
     */
    interface MainMenuF {
        List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator);
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
     * Context-menu extension for the sequent term menu: contributes {@link MenuItem}s for the
     * clicked position (Swing {@code KeYGuiExtension.ContextMenu},
     * KeYGuiExtension.java:145-168 with {@code ContextMenuKind.SEQUENT_VIEW} — the FX port
     * exposes only the sequent slot because it is the only term-menu slot). The host renders
     * the items inside the "Extensions" section of the sequent context menu.
     *
     * @param mediator the mediator of the window
     * @param goal the goal whose sequent was clicked
     * @param pos the clicked position
     * @return non-null, emptiable list of menu items
     */
    interface ContextMenuF {
        List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
                PosInSequent pos);
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
     * position (Swing {@code KeYGuiExtension.Tooltip}, KeYGuiExtension.java:186-201). The FX
     * host integration with the sequent view tooltips is a later milestone; the facade already
     * aggregates the strings.
     *
     * @param mediator the mediator of the window
     * @param pos the position of the term whose info shall be shown
     * @return non-null, emptiable list of strings
     */
    interface TooltipF {
        List<String> getTooltipStrings(KeYMediatorF mediator, PosInSequent pos);
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
