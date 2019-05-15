package de.uka.ilkd.key.gui;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.DefaultSingleCDockable;
import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import bibliothek.gui.dock.common.intern.CDockable;
import bibliothek.gui.dock.util.IconManager;
import bibliothek.gui.dock.util.Priority;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.settings.PathConfig;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.EventObject;

/**
 * @author Alexander Weigl
 * @version 1 (15.05.19)
 */
public final class DockingHelper {
    public static float SIZE_ICON_DOCK = 12f;
    public static File LAYOUT_FILE = new File(PathConfig.getKeyConfigDir(), "layout.xml");

    public static String DEFAULT_LAYOUT = "default";
    public static String ALT_1_LAYOUT = "alternative1";
    public static String ALT_2_LAYOUT = "alternative2";

    static CDockable createDock(TabPanel p) {
        CAction[] actions =
                p.getTitleActions().stream().map(DockingHelper::translateAction)
                        .toArray(CAction[]::new);

        return new DefaultSingleCDockable(p.getClass().getName(),
                p.getIcon(), p.getTitle(), p.getComponent(),
                p.getPermissions(), actions);
    }

    static CAction translateAction(Action action) {
        CButton button = new CButton(
                (String) action.getValue(Action.NAME),
                (Icon) action.getValue(Action.SMALL_ICON));
        button.addActionListener(action);
        button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
        button.setEnabled(action.isEnabled());

        action.addPropertyChangeListener(evt -> {
            button.setText((String) action.getValue(Action.NAME));
            button.setIcon((Icon) action.getValue(Action.SMALL_ICON));
            button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
            button.setEnabled(action.isEnabled());
        });

        return button;
    }

    public static void configure(MainWindow mw) {
        CControl globalPort = mw.getDockControl();
        IconManager icons = globalPort.getController().getIcons();
        Priority p = Priority.CLIENT;

        icons.setIcon("locationmanager.normalize", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_RESTORE, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.maximize", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_MAXIMIZE, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.minimize", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_MINIMIZE, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.externalize", p,
                IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_SQUARE_ALT, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.unexternalize", p,
                IconFontSwing.buildIcon(FontAwesomeSolid.MOUSE_POINTER, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.unmaximize_externalized", p,
                IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT, SIZE_ICON_DOCK));

        icons.setIcon("screen.maximize", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.EDIT, SIZE_ICON_DOCK));

        icons.setIcon("close", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_CLOSE, SIZE_ICON_DOCK));

        installActions(mw);

        loadLayouts(globalPort);

        //loading of the default layout if defined
        boolean defaultLayoutDefined =
                Arrays.stream(globalPort.layouts())
                        .anyMatch(it -> DEFAULT_LAYOUT.equals(it));
        if (defaultLayoutDefined) {
            globalPort.load(DEFAULT_LAYOUT);
        }

        mw.getMediator().addGUIListener(new GUIListener() {
            @Override
            public void modalDialogOpened(EventObject e) {

            }

            @Override
            public void modalDialogClosed(EventObject e) {

            }

            @Override
            public void shutDown(EventObject e) {
                try {
                    globalPort.writeXML(LAYOUT_FILE);
                } catch (IOException ex) {
                    ex.printStackTrace();
                }
            }
        });
    }

    private static void loadLayouts(CControl globalPort) {
        try {
            if (LAYOUT_FILE.exists()) {
                globalPort.readXML(LAYOUT_FILE);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void installActions(MainWindow mw) {
        KeyAction[] actions = new KeyAction[]{
                new LoadLayoutAction(mw, DEFAULT_LAYOUT, KeyEvent.VK_F11),
                new LoadLayoutAction(mw, ALT_1_LAYOUT, KeyEvent.VK_F12),
                //new LoadLayoutAction(mw, ALT_2_LAYOUT, KeyEvent.VK_F7),

                new SaveLayoutAction(mw, DEFAULT_LAYOUT, KeyEvent.VK_F11),
                new SaveLayoutAction(mw, ALT_1_LAYOUT, KeyEvent.VK_F12)
                //new SaveLayoutAction(mw, ALT_2_LAYOUT, KeyEvent.VK_F7)
        };

        JPanel comp = (JPanel) mw.getContentPane();
        for (KeyAction action : actions) {
            comp.registerKeyboardAction(action, action.getAcceleratorKey(),
                    JComponent.WHEN_IN_FOCUSED_WINDOW);
        }
    }

    static class SaveLayoutAction extends MainWindowAction {
        private final String layoutName;

        public SaveLayoutAction(MainWindow mainWindow, String name, int key) {
            super(mainWindow);
            this.layoutName = name;
            setName("Save Layout");
            setAcceleratorKey(KeyStroke.getKeyStroke(key,
                    InputEvent.CTRL_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK));
            KeyStrokeManager.lookupAndOverride(this,
                    getClass().getName() + "$" + layoutName);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            mainWindow.getDockControl().save(layoutName);
            mainWindow.setStatusLine("Layout save at " + layoutName);
        }
    }

    static class LoadLayoutAction extends MainWindowAction {
        private final String layoutName;

        public LoadLayoutAction(MainWindow mainWindow, String name, int key) {
            super(mainWindow);
            this.layoutName = name;
            setName("Load Layout");
            setAcceleratorKey(KeyStroke.getKeyStroke(key, InputEvent.CTRL_DOWN_MASK));
            KeyStrokeManager.lookupAndOverride(this,
                    getClass().getName() + "$" + layoutName);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            boolean defaultLayoutDefined = Arrays.asList(mainWindow.getDockControl().layouts())
                    .contains(layoutName);
            if (defaultLayoutDefined) {
                mainWindow.getDockControl().load(layoutName);
                mainWindow.setStatusLine("Layout " + layoutName + " loaded");
            } else {
                mainWindow.setStatusLine("Layout " + layoutName + " could not be found.");
            }
        }
    }
}
