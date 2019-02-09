package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import java.awt.*;
import java.util.*;
import java.util.List;
import java.util.function.ToIntFunction;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import static de.uka.ilkd.key.gui.ext.KeYMainMenu.PATH;
import static de.uka.ilkd.key.gui.ext.KeYMainMenu.PRIORITY;

/**
 * @author Alexander Weigl
 * @version 1 (07.02.19)
 */
public final class KeYGuiExtensionFacade {
    @SuppressWarnings("todo")
    public static List<KeYPane> getAllPanels() {
        Spliterator<KeYPane> iter = ServiceLoader.load(KeYPane.class).spliterator();
        return StreamSupport.stream(iter, false)
                .sorted(Comparator.comparingInt(KeYPane::priority))
                .collect(Collectors.toList());
    }

    public static <T extends KeYPane> Optional<T> getPanel(Class<T> clazz) {
        Optional<KeYPane> v = getAllPanels().stream()
                .filter(it -> it.getClass().isAssignableFrom(clazz))
                .findAny();
        return (Optional<T>) v;
    }

    public static List<KeYMainMenu> getMainMenuExtensions() {
        Spliterator<KeYMainMenu> iter = ServiceLoader.load(KeYMainMenu.class).spliterator();
        return StreamSupport.stream(iter, false)
                //.flatMap(it -> it.getActions().stream())
                .sorted(Comparator.comparingInt(KeYMainMenu::getPriority))
                .collect(Collectors.toList());
    }

    /*
    public static Optional<Action> getMainMenuExtensions(String name) {
        Spliterator<KeYMainMenu> iter = ServiceLoader.load(KeYMainMenu.class).spliterator();
        return StreamSupport.stream(iter, false)
                .flatMap(it -> it.getActions(mainWindow).stream())
                .filter(Objects::nonNull)
                .filter(it -> it.getValue(Action.NAME).equals(name))
                .findAny();
    }*/

    public static JMenu getExtensionMenu(MainWindow mainWindow) {
        ToIntFunction<Action> func = (Action a) -> {
            Integer i = (Integer) a.getValue(PRIORITY);
            if (i == null) return 0;
            else return i;
        };

        List<KeYMainMenu> kmm = getMainMenuExtensions();
        JMenu menu = new JMenu("Extensions");
        for (KeYMainMenu it : kmm) {
            List<Action> actions = it.getActions(mainWindow);
            actions.sort(Comparator.comparingInt(func));
            for (Action act : actions) {
                Object path = act.getValue(PATH);
                String spath;
                if (path == null) spath = "";
                else spath = path.toString();
                Iterator<String> mpath = Pattern.compile(Pattern.quote(".")).splitAsStream(spath).iterator();
                JMenu a = findMenu(menu, mpath);
                a.add(act);
            }
        }
        return menu;
    }

    private static JMenu findMenu(JMenu menu, Iterator<String> mpath) {
        if (mpath.hasNext()) {
            String cur = mpath.next();
            Component[] children = menu.getMenuComponents();
            for (int i = 0; i < children.length; i++) {
                if (children[i].getName().equals(cur)) {
                    return (JMenu) children[i];
                }
            }
            JMenu m = new JMenu(cur);
            m.setName(cur);
            menu.add(m);
            return findMenu(m, mpath);
        } else
            return menu;
    }
}
