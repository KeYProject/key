/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.awt.*;
import java.util.*;
import java.util.List;
import java.util.function.ToIntFunction;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;

/**
 * Facade for retrieving the GUI extensions.
 *
 * @author Alexander Weigl
 * @version 1 (07.02.19)
 */
public final class KeYGuiExtensionFacade {
    private static final Set<String> forbiddenPlugins = new HashSet<>();
    private static List<Extension<?>> extensions = new LinkedList<>();
    // private static Map<Class<?>, List<Object>> extensionCache = new HashMap<>();

    // region panel extension
    public static Stream<TabPanel> getAllPanels(MainWindow window) {
        return getLeftPanel().stream()
                .flatMap(it -> it.getPanels(window, window.getMediator()).stream());
    }

    public static List<KeYGuiExtension.LeftPanel> getLeftPanel() {
        return getExtensionInstances(KeYGuiExtension.LeftPanel.class);
    }
    // endregion

    // region main menu extension

    /**
     * Retrieves all known implementation of the {@link KeYGuiExtension.MainMenu}
     *
     * @return a list
     */
    public static List<KeYGuiExtension.MainMenu> getMainMenuExtensions() {
        return getExtensionInstances(KeYGuiExtension.MainMenu.class);
    }

    public static Stream<Action> getMainMenuActions(MainWindow mainWindow) {
        ToIntFunction<Action> func = (Action a) -> {
            Integer i = (Integer) a.getValue(KeyAction.PRIORITY);
            if (i == null) {
                return 0;
            } else {
                return i;
            }
        };

        return KeYGuiExtensionFacade.getMainMenuExtensions().stream()
                .flatMap(it -> it.getMainMenuActions(mainWindow).stream())
                .sorted(Comparator.comparingInt(func));
    }

    /**
     * Adds all registered and activated {@link KeYGuiExtension.MainMenu} to the given menuBar.
     *
     * @return a menu
     */
    public static void addExtensionsToMainMenu(MainWindow mainWindow, JMenuBar menuBar) {
        JMenu menu = new JMenu("Extensions");
        getMainMenuActions(mainWindow).forEach(it -> sortActionIntoMenu(it, menuBar, menu));

        if (menu.getMenuComponents().length > 0) {
            menuBar.add(menu);
        }

    }

    // region Menu Helper

    private static Iterator<String> getMenuPath(Action act) {
        Object path = act.getValue(KeyAction.PATH);
        String spath;
        if (path == null) {
            spath = "";
        } else {
            spath = path.toString();
        }
        return Pattern.compile(Pattern.quote(".")).splitAsStream(spath).iterator();
    }

    private static void sortActionIntoMenu(Action act, JMenu menu) {
        Iterator<String> mpath = getMenuPath(act);
        JMenu a = findMenu(menu, mpath);

        if (Boolean.TRUE.equals(act.getValue(KeyAction.CHECKBOX))) {
            a.add(new JCheckBoxMenuItem(act));
        } else {
            a.add(act);
        }
    }

    private static void sortActionIntoMenu(Action act, JPopupMenu menu) {
        Iterator<String> mpath = getMenuPath(act);
        JMenu a = findMenu(menu, mpath);

        if (Boolean.TRUE.equals(act.getValue(KeyAction.CHECKBOX))) {
            if (a == null) {
                menu.add(new JCheckBoxMenuItem(act));
            } else {
                a.add(new JCheckBoxMenuItem(act));
            }
        } else {
            if (a == null) {
                menu.add(act);
            } else {
                a.add(act);
            }
        }
    }

    private static void sortActionIntoMenu(Action act, JMenuBar menuBar, JMenu defaultMenu) {
        Iterator<String> mpath = getMenuPath(act);
        JMenu a = findMenu(menuBar, mpath, defaultMenu);

        if (Boolean.TRUE.equals(act.getValue(KeyAction.CHECKBOX))) {
            a.add(new JCheckBoxMenuItem(act));
        } else {
            a.add(act);
        }
    }

    private static JMenu findMenu(JMenuBar menuBar, Iterator<String> mpath, JMenu defaultMenu) {
        if (mpath.hasNext()) {
            String cur = mpath.next();
            for (int i = 0; i < menuBar.getMenuCount(); i++) {
                JMenu menu = menuBar.getMenu(i);
                if (Objects.equals(menu.getText(), cur)) {
                    return findMenu(menu, mpath);
                }
            }
            JMenu menu = new JMenu(cur);
            menu.setName(cur);
            menuBar.add(menu);
            return findMenu(menu, mpath);
        }
        return defaultMenu;
    }

    private static JMenu findMenu(JPopupMenu menu, Iterator<String> mpath) {
        if (mpath.hasNext()) {
            String cur = mpath.next();
            Component[] children = menu.getComponents();
            for (Component child : children) {
                if (Objects.equals(child.getName(), cur)) {
                    JMenu sub = (JMenu) child;
                    return findMenu(sub, mpath);
                }
            }
            JMenu m = new JMenu(cur);
            m.setName(cur);
            menu.add(m);
            return findMenu(m, mpath);
        } else {
            return null;
        }
    }

    private static JMenu findMenu(JMenu menu, Iterator<String> mpath) {
        if (mpath.hasNext()) {
            String cur = mpath.next();
            Component[] children = menu.getMenuComponents();
            for (Component child : children) {
                if (Objects.equals(child.getName(), cur)) {
                    JMenu sub = (JMenu) child;
                    return findMenu(sub, mpath);
                }
            }
            JMenu m = new JMenu(cur);
            m.setName(cur);
            menu.add(m);
            return findMenu(m, mpath);
        } else {
            return menu;
        }
    }
    // endregion

    /**
     * Retrieves all known implementation of the {@link KeYGuiExtension.Toolbar}
     *
     * @return a list
     */
    public static List<KeYGuiExtension.Toolbar> getToolbarExtensions() {
        return getExtensionInstances(KeYGuiExtension.Toolbar.class);
    }
    // endregion

    /**
     * Creates all toolbars for the known extension.
     *
     * @param mainWindow non-null
     * @return
     */
    public static List<JToolBar> createToolbars(MainWindow mainWindow) {
        return getToolbarExtensions().stream().map(it -> it.getToolbar(mainWindow))
                .peek(x -> x.setFloatable(false))
                .collect(Collectors.toList());
    }

    /**
     * Retrieves all known implementation of the {@link KeYGuiExtension.MainMenu}
     *
     * @return a list
     */
    public static List<KeYGuiExtension.ContextMenu> getContextMenuExtensions() {
        return getExtensionInstances(KeYGuiExtension.ContextMenu.class);
    }

    public static JPopupMenu createContextMenu(ContextMenuKind kind, Object underlyingObject,
            KeYMediator mediator) {
        JPopupMenu menu = new JPopupMenu();
        if (underlyingObject instanceof Proof) {
            for (Component comp : MainWindow.getInstance().createProofMenu((Proof) underlyingObject)
                    .getMenuComponents()) {
                menu.add(comp);
            }
        }
        List<Action> content = getContextMenuItems(kind, underlyingObject, mediator);
        content.forEach(menu::add);
        return menu;
    }

    public static void addContextMenuItems(ContextMenuKind kind, JPopupMenu menu,
            Object underlyingObject, KeYMediator mediator) {
        getContextMenuItems(kind, underlyingObject, mediator)
                .forEach(it -> sortActionIntoMenu(it, menu));
    }

    public static List<Action> getContextMenuItems(ContextMenuKind kind, Object underlyingObject,
            KeYMediator mediator) {
        if (!kind.getType().isAssignableFrom(underlyingObject.getClass())) {
            throw new IllegalArgumentException();
        }

        return getContextMenuExtensions().stream()
                .flatMap(it -> it.getContextActions(mediator, kind, underlyingObject).stream())
                .collect(Collectors.toList());
    }

    public static JMenu createTermMenu(ContextMenuKind kind, Object underlyingObject,
            KeYMediator mediator) {
        JMenu menu = new JMenu("Extensions");
        getContextMenuItems(kind, underlyingObject, mediator)
                .forEach(it -> sortActionIntoMenu(it, menu));
        return menu;
    }

    private static void loadExtensions() {
        extensions = ServiceLoader.load(KeYGuiExtension.class).stream()
                .map(ServiceLoader.Provider::type).filter(KeYGuiExtensionFacade::isNotForbidden)
                .distinct().map(Extension::new).sorted().collect(Collectors.toList());
    }

    /**
     * @param clazz the interface class
     * @param <T> the interface of the service
     * @return a list of all found and enabled service implementations
     */
    @SuppressWarnings("unchecked")
    private static <T> Stream<Extension<T>> getExtensionsStream(Class<T> clazz) {
        return getExtensions().stream().filter(it -> !it.isDisabled())
                .filter(it -> clazz.isAssignableFrom(it.getType())).map(it -> (Extension<T>) it);
    }

    private static <T> List<T> getExtensionInstances(Class<T> c) {
        return getExtensionsStream(c).map(Extension::getInstance).collect(Collectors.toList());
    }

    /**
     * Determines if a given plugin is completely disabled.
     * <p>
     * A plugin can either disabled by adding its fqn to the {@see #forbiddenPlugins} list or
     * setting <code>-P[fqn]=false</code> add the command line.
     *
     * @param a an instance of a plugin, non-null
     * @return
     */
    private static <T> boolean isNotForbidden(Class<T> a) {
        if (forbiddenPlugins.contains(a.getName())) {
            return false;
        }
        String sys = System.getProperty(a.getName());
        return sys == null || !sys.equalsIgnoreCase("false");
    }
    // endregion

    public static List<Extension<?>> getExtensions() {
        if (extensions.isEmpty()) {
            loadExtensions();
        }
        return extensions;
    }

    public static List<JComponent> getStatusLineComponents() {
        return getStatusLineExtensions().stream()
                .flatMap(it -> it.getStatusLineComponents().stream()).collect(Collectors.toList());

    }

    public static List<KeYGuiExtension.StatusLine> getStatusLineExtensions() {
        return getExtensionInstances(KeYGuiExtension.StatusLine.class);
    }

    public static Collection<KeYGuiExtension.Settings> getSettingsProvider() {
        return getExtensionInstances(KeYGuiExtension.Settings.class);
    }

    public static List<KeYGuiExtension.Startup> getStartupExtensions() {
        return getExtensionInstances(KeYGuiExtension.Startup.class);
    }


    // region keyboard shortcuts
    public static List<KeYGuiExtension.KeyboardShortcuts> getKeyboardShortcutsExtensions() {
        return getExtensionInstances(KeYGuiExtension.KeyboardShortcuts.class);
    }

    public static Stream<Action> getKeyboardShortcuts(KeYMediator mediator, String componentId,
            JComponent component) {
        return getKeyboardShortcutsExtensions().stream()
                .flatMap(it -> it.getShortcuts(mediator, componentId, component).stream())
                .sorted(new ActionPriorityComparator());
    }

    /**
     * @param mediator
     * @param component
     * @param componentId
     */
    public static void installKeyboardShortcuts(KeYMediator mediator, JComponent component,
            String componentId) {
        Stream<Action> provider = getKeyboardShortcuts(mediator, componentId, component);
        provider.forEach(it -> {
            int condition = it.getValue(KeyAction.SHORTCUT_FOCUSED_CONDITION) != null
                    ? (int) it.getValue(KeyAction.SHORTCUT_FOCUSED_CONDITION)
                    : JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT;

            KeyStroke ks = (KeyStroke) (it.getValue(KeyAction.LOCAL_ACCELERATOR) != null
                    ? it.getValue(KeyAction.LOCAL_ACCELERATOR)
                    : it.getValue(Action.ACCELERATOR_KEY));

            component.registerKeyboardAction(it, ks, condition);
        });
    }
    // endregion

    // region Term tool tip

    /**
     * Retrieves all known implementations of the {@link KeYGuiExtension.Tooltip}.
     *
     * @return all known implementations of the {@link KeYGuiExtension.Tooltip}.
     */
    public static List<KeYGuiExtension.Tooltip> getTooltipExtensions() {
        return getExtensionInstances(KeYGuiExtension.Tooltip.class);
    }

    /**
     *
     * @param window the main window.
     * @param pos the position the user selected.
     * @return every term info string from every loaded extension.
     */
    public static List<String> getTooltipStrings(MainWindow window, PosInSequent pos) {
        return getTooltipExtensions().stream()
                .flatMap(it -> it.getTooltipStrings(window, pos).stream())
                .collect(Collectors.toList());
    }
    // endregion


    public static Stream<String> getTermInfoStrings(MainWindow mainWindow, PosInSequent mousePos) {
        return getExtensionInstances(KeYGuiExtension.TermInfo.class).stream()
                .flatMap(it -> it.getTermInfoStrings(mainWindow, mousePos).stream());
    }

    /**
     * Disables the clazz from further loading.
     * <p>
     * If this extension is already loaded, it will be removed from the list of extensions. This
     * does not include a removal from the GUI in all cases.
     *
     * @param clazz a fqdn of a class
     */
    public void forbidClass(String clazz) {
        forbiddenPlugins.add(clazz);
        extensions = extensions.stream().filter(it -> !it.getType().getName().equals(clazz))
                .collect(Collectors.toList());
    }

    /**
     * removes a class from the forbidden list.
     * <p>
     * Without a plugin lifecycle this is very useless.
     * </p>
     *
     * @param clazz
     */
    public void allowClass(String clazz) {
        forbiddenPlugins.remove(clazz);
    }

    private static class ActionPriorityComparator implements Comparator<Action> {
        @Override
        public int compare(Action o1, Action o2) {
            int a = getPriority(o1);
            int b = getPriority(o2);
            return a - b;
        }

        private int getPriority(Action action) {
            if (action.getValue(KeyAction.PRIORITY) != null) {
                return (int) action.getValue(KeyAction.PRIORITY);
            }
            return 0;
        }
    }
}
