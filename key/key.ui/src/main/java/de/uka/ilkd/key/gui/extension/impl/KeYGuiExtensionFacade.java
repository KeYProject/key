package de.uka.ilkd.key.gui.extension.impl;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.key_project.util.ServiceLoaderUtil;

import javax.swing.*;
import java.awt.*;
import java.util.List;
import java.util.*;
import java.util.function.ToIntFunction;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static de.uka.ilkd.key.gui.extension.api.KeYExtConstants.PATH;
import static de.uka.ilkd.key.gui.extension.api.KeYExtConstants.PRIORITY;

/**
 * Facade for retrieving the GUI extensions.
 *
 * @author Alexander Weigl
 * @version 1 (07.02.19)
 */
public final class KeYGuiExtensionFacade {
    private static final Set<String> forbiddenPlugins = new HashSet<>();
    private static List<Extension> extensions = new LinkedList<>();
    //private static Map<Class<?>, List<Object>> extensionCache = new HashMap<>();

    //region panel extension
    @SuppressWarnings("todo")
    public static Stream<TabPanel> getAllPanels(MainWindow window) {
        return getLeftPanel().stream().flatMap(it -> it.getPanels(window, window.getMediator()).stream());
    }

    public static List<KeYGuiExtension.LeftPanel> getLeftPanel() {
        return getExtensionInstances(KeYGuiExtension.LeftPanel.class);
    }

    /**
     * Retrieves all known implementation of the {@link KeYGuiExtension.MainMenu}
     *
     * @return a list
     */
    public static List<KeYGuiExtension.MainMenu> getMainMenuExtensions() {
        return getExtensionInstances(KeYGuiExtension.MainMenu.class);
    }
    //endregion

    //region main menu extension

    /**
     * Creates the extension menu of all known {@link KeYGuiExtension.MainMenu}.
     *
     * @return a menu
     */
    public static JMenu createExtensionMenu(MainWindow mainWindow) {
        ToIntFunction<Action> func = (Action a) -> {
            Integer i = (Integer) a.getValue(PRIORITY);
            if (i == null) return 0;
            else return i;
        };

        List<KeYGuiExtension.MainMenu> kmm = getMainMenuExtensions();
        JMenu menu = new JMenu("Extensions");
        for (KeYGuiExtension.MainMenu it : kmm) {
            List<Action> actions = it.getMainMenuActions(mainWindow);
            actions.sort(Comparator.comparingInt(func));
            sortActionsIntoMenu(actions, menu);
        }
        return menu;
    }

    /*
    public static Optional<Action> getMainMenuExtensions(String name) {
        Spliterator<KeYGuiExtension.MainMenu> iter = ServiceLoader.load(KeYGuiExtension.MainMenu.class).spliterator();
        return StreamSupport.stream(iter, false)
                .flatMap(it -> it.getMainMenuActions(mainWindow).stream())
                .filter(Objects::nonNull)
                .filter(it -> it.getValue(Action.NAME).equals(name))
                .findAny();
    }*/

    //region Menu Helper
    private static void sortActionsIntoMenu(List<Action> actions, JMenu menu) {
        actions.forEach(act -> sortActionIntoMenu(act, menu));
    }
    //endregion

    private static void sortActionIntoMenu(Action act, JMenu menu) {
        Object path = act.getValue(PATH);
        String spath;
        if (path == null) spath = "";
        else spath = path.toString();
        Iterator<String> mpath = Pattern.compile(Pattern.quote(".")).splitAsStream(spath).iterator();
        JMenu a = findMenu(menu, mpath);
        a.add(act);
    }

    private static JMenu findMenu(JMenu menu, Iterator<String> mpath) {
        if (mpath.hasNext()) {
            String cur = mpath.next();
            Component[] children = menu.getMenuComponents();
            for (int i = 0; i < children.length; i++) {
                if (Objects.equals(children[i].getName(), cur)) {
                    JMenu sub = (JMenu) children[i];
                    return findMenu(sub, mpath);
                }
            }
            JMenu m = new JMenu(cur);
            m.setName(cur);
            menu.add(m);
            return findMenu(m, mpath);
        } else
            return menu;
    }

    /**
     * Retrieves all known implementation of the {@link KeYGuiExtension.Toolbar}
     *
     * @return a list
     */
    public static List<KeYGuiExtension.Toolbar> getToolbarExtensions() {
        return getExtensionInstances(KeYGuiExtension.Toolbar.class);
    }
    //endregion

    /**
     * Creates all toolbars for the known extension.
     *
     * @param mainWindow non-null
     * @return
     */
    public static List<JToolBar> createToolbars(MainWindow mainWindow) {
        return getToolbarExtensions().stream()
                .map(it -> it.getToolbar(mainWindow))
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

    public static <T> List<Action> getContextMenuFor(ContextMenuKind kind, T underlyingObject,
                                                     MainWindow window) {
        if (!kind.getType().isAssignableFrom(underlyingObject.getClass())) {
            throw new IllegalArgumentException();
        }

        return getContextMenuExtensions().stream()
                .flatMap(it -> it.getContextActions(window, kind, underlyingObject).stream())
                .collect(Collectors.toList());
    }

    public static <T> JMenu createTermMenu(ContextMenuKind kind, T underlyingObject, MainWindow window) {
        JMenu menu = new JMenu("Extensions");
        getContextMenuFor(kind, underlyingObject, window)
                .forEach(it -> sortActionIntoMenu(it, menu));
        return menu;
    }

    @SuppressWarnings("unchecked")
    private static void loadExtensions() {
        extensions = ServiceLoaderUtil.stream(KeYGuiExtension.class)
                .filter(KeYGuiExtensionFacade::isNotForbidden)
                .map(Extension::new)
                .sorted()
                .distinct()
                .collect(Collectors.toList());
    }

    /**
     * @param clazz the interface class
     * @param <T>   the interface of the service
     * @return a list of all found and enabled service implementations
     */
    @SuppressWarnings("unchecked")
    private static <T> Stream<Extension<T>> getExtensionsStream(Class<T> clazz) {
        return getExtensions().stream()
                .filter(it -> !it.isDisabled())
                .filter(it -> clazz.isAssignableFrom(it.getType()))
                .map(it -> (Extension<T>) it);
    }

    private static <T> List<T> getExtensionInstances(Class<T> c) {
        return getExtensionsStream(c).map(Extension::getInstance)
                .collect(Collectors.toList());
    }

    /**
     * Determines if a given plugin is completely disabled.
     * <p>
     * A plugin can either disabled by adding its fqn to the {@see #forbiddenPlugins} list
     * or setting <code>-P[fqn]=false</code> add the command line.
     *
     * @param a an instance of a plugin, non-null
     * @return
     */
    private static <T> boolean isNotForbidden(Class<T> a) {
        if (forbiddenPlugins.contains(a.getName()))
            return false;
        String sys = System.getProperty(a.getName());
        return sys == null || !sys.equalsIgnoreCase("false");
    }
    //endregion

    public static List<Extension> getExtensions() {
        if (extensions.isEmpty())
            loadExtensions();
        return extensions;
    }

    public static List<JComponent> getStatusLineComponents() {
        return getStatusLineExtensions().stream()
                .flatMap(it -> it.getStatusLineComponents().stream())
                .collect(Collectors.toList());

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

    /**
     * Disables the clazz from further loading.
     * <p>
     * If this extension is already loaded, it will be removed
     * from the list of extensions. This does not include a removal
     * from the GUI in all cases.
     *
     * @param clazz a fqdn of a class
     */
    public void forbidClass(String clazz) {
        forbiddenPlugins.add(clazz);
        extensions = extensions.stream()
                .filter(it -> !it.getType().getName().equals(clazz))
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
}
