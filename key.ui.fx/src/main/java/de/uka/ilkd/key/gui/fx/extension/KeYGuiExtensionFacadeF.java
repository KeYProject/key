/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.ServiceLoader;
import java.util.stream.Collectors;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tab;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;

import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Facade for retrieving the FX GUI extensions, counter-part of {@code
 * de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade} of the Swing module {@code key.ui}
 * (KeYGuiExtensionFacade.java:36-461). Discovers all {@link KeYGuiExtensionF} providers lazily
 * (cached on first use) and aggregates the contributions of the typed capability interfaces.
 * Never returns {@code null} — empty lists instead.
 *
 * @author Alexander Weigl
 * @author MP9.0 extension SPI port (FX)
 */
@NullMarked
public final class KeYGuiExtensionFacadeF {

    private static final Logger LOGGER = LoggerFactory.getLogger(KeYGuiExtensionFacadeF.class);

    private static List<KeYGuiExtensionF> extensions;

    private KeYGuiExtensionFacadeF() {
    }

    /**
     * The discovered extension providers, loaded lazily on first use and cached (Swing
     * {@code KeYGuiExtensionFacade.getExtensions}, KeYGuiExtensionFacade.java:318-323). The
     * providers are sorted by their {@link KeYGuiExtensionF.Info#priority()} (lowest first,
     * baseline zero), mirroring the Swing priority sort of the main-menu actions
     * (KeYGuiExtensionFacade.java:63-76).
     *
     * @return the non-null, possibly empty list of providers
     */
    public static List<KeYGuiExtensionF> getExtensions() {
        if (extensions == null) {
            extensions = ServiceLoader.load(KeYGuiExtensionF.class).stream()
                    .map(ServiceLoader.Provider::get)
                    .filter(Objects::nonNull)
                    .sorted(Comparator.comparingInt(KeYGuiExtensionFacadeF::priorityOf))
                    .collect(Collectors.toList());
            LOGGER.info("Extension discovery: {} FX extension(s) loaded: {}",
                extensions.size(),
                extensions.stream().map(it -> it.getClass().getName())
                        .collect(Collectors.joining(", ")));
        }
        return extensions;
    }

    /**
     * @return the number of discovered (and instantiated) extension providers — the assertion
     *         target of the {@code key.fx.verify.extensions} self test
     */
    public static int discoveredCount() {
        return getExtensions().size();
    }

    /** @return the {@link KeYGuiExtensionF.Info#priority()} of the provider's class, or 0. */
    private static int priorityOf(KeYGuiExtensionF extension) {
        KeYGuiExtensionF.Info info =
            extension.getClass().getAnnotation(KeYGuiExtensionF.Info.class);
        return info == null ? 0 : info.priority();
    }

    /**
     * The menus contributed by every {@link KeYGuiExtensionF.MainMenuF} provider, in provider
     * order (Swing {@code KeYGuiExtensionFacade.getMainMenuActions},
     * KeYGuiExtensionFacade.java:63-76). The host appends these to the menu bar as separate
     * menus after the built-in menus; the five built-in menus' item sets are untouched (Swing
     * {@code MainWindow.createMenuBar}, MainWindow.java:977-988 + {@code
     * addExtensionsToMainMenu}, KeYGuiExtensionFacade.java:81-89).
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of menus
     */
    public static List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        List<Menu> menus = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.MainMenuF mainMenu) {
                menus.addAll(mainMenu.getMenus(window, mediator));
            }
        }
        return menus;
    }

    /**
     * The toolbar controls contributed by every {@link KeYGuiExtensionF.ToolbarF} provider
     * (Swing {@code KeYGuiExtensionFacade.createToolbars}, KeYGuiExtensionFacade.java:217-221).
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of controls
     */
    public static List<Control> getToolbarControls(MainWindowF window, KeYMediatorF mediator) {
        List<Control> controls = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.ToolbarF toolbar) {
                controls.addAll(toolbar.getToolbarControls(window, mediator));
            }
        }
        return controls;
    }

    /**
     * The status-line controls contributed by every {@link KeYGuiExtensionF.StatusLineF}
     * provider (Swing {@code KeYGuiExtensionFacade.getStatusLineComponents},
     * KeYGuiExtensionFacade.java:325-333).
     *
     * @return non-null, emptiable list of controls
     */
    public static List<Control> getStatusLineControls() {
        List<Control> controls = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.StatusLineF statusLine) {
                controls.addAll(statusLine.getStatusLineControls());
            }
        }
        return controls;
    }

    /**
     * The left-panel tabs contributed by every {@link KeYGuiExtensionF.LeftPanelF} provider
     * (Swing {@code KeYGuiExtensionFacade.getAllPanels}, KeYGuiExtensionFacade.java:42-45).
     *
     * @param window the main window
     * @param mediator the mediator of the window
     * @return non-null, emptiable list of tabs
     */
    public static List<Tab> getLeftPanelTabs(MainWindowF window, KeYMediatorF mediator) {
        List<Tab> tabs = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.LeftPanelF leftPanel) {
                tabs.addAll(leftPanel.getLeftPanelTabs(window, mediator));
            }
        }
        return tabs;
    }

    /**
     * The sequent context-menu items contributed by every {@link
     * KeYGuiExtensionF.ContextMenuF} provider for the given goal and position (Swing
     * {@code KeYGuiExtensionFacade.getContextMenuItems},
     * KeYGuiExtensionFacade.java:264-269 with {@code ContextMenuKind.SEQUENT_VIEW}).
     *
     * @param mediator the mediator of the window
     * @param goal the goal whose sequent was clicked
     * @param pos the clicked position
     * @return non-null, emptiable list of menu items
     */
    public static List<MenuItem> getSequentContextItems(KeYMediatorF mediator, Goal goal,
            PosInSequent pos) {
        List<MenuItem> items = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.ContextMenuF contextMenu) {
                items.addAll(contextMenu.getSequentContextItems(mediator, goal, pos));
            }
        }
        return items;
    }

    /**
     * The settings providers contributed by every {@link KeYGuiExtensionF.SettingsF} provider
     * (Swing {@code KeYGuiExtensionFacade.getSettingsProvider},
     * KeYGuiExtensionFacade.java:335-337); the host registers them into the
     * {@link de.uka.ilkd.key.gui.fx.settings.SettingsManagerF} registry.
     *
     * @return non-null, emptiable list of providers
     */
    public static List<SettingsProviderF> getSettingsProviders() {
        List<SettingsProviderF> providers = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.SettingsF settings) {
                providers.add(settings.getSettings());
            }
        }
        return providers;
    }

    /**
     * The tooltip strings contributed by every {@link KeYGuiExtensionF.TooltipF} provider for
     * the given position (Swing {@code KeYGuiExtensionFacade.getTooltipStrings},
     * KeYGuiExtensionFacade.java:395-399).
     *
     * @param mediator the mediator of the window
     * @param pos the position of the term whose info shall be shown
     * @return non-null, emptiable list of strings
     */
    public static List<String> getTooltipStrings(KeYMediatorF mediator, PosInSequent pos) {
        List<String> strings = new ArrayList<>();
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.TooltipF tooltip) {
                strings.addAll(tooltip.getTooltipStrings(mediator, pos));
            }
        }
        return strings;
    }

    /**
     * Calls {@link KeYGuiExtensionF.StartupF#init} of every provider once at app startup
     * (Swing {@code KeYGuiExtensionFacade.getStartupExtensions} + the host calling
     * {@code init}, KeYGuiExtensionFacade.java:339-341; Swing MainWindow calls
     * {@code extension.init(this, mediator)} on the Startup extensions after the facade
     * creation).
     *
     * @param window the main window
     * @param mediator the mediator of the window
     */
    public static void initAll(MainWindowF window, KeYMediatorF mediator) {
        for (KeYGuiExtensionF extension : getExtensions()) {
            if (extension instanceof KeYGuiExtensionF.StartupF startup) {
                startup.init(window, mediator);
            }
        }
    }
}
