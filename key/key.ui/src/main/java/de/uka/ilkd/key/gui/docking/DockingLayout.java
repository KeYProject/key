package de.uka.ilkd.key.gui.docking;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.util.IconManager;
import bibliothek.gui.dock.util.Priority;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.settings.PathConfig;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.*;

/**
 * Extension for working with layouts.
 *
 * @author Alexander Weigl
 * @version 1 (15.05.19)
 */
@KeYGuiExtension.Info(name = "Docking Helpers", optional = false, experimental = false)
public final class DockingLayout
        implements KeYGuiExtension,
        KeYGuiExtension.Startup,
        KeYGuiExtension.MainMenu,
        KeYGuiExtension.Toolbar {

    public static final File LAYOUT_FILE = new File(PathConfig.getKeyConfigDir(), "layout.xml");
    public static final String[] LAYOUT_NAMES = new String[]{"default", "slot 1", "slot 2"};
    public static final int[] LAYOUT_KEYS = new int[]{KeyEvent.VK_F11, KeyEvent.VK_F12};
    public static float SIZE_ICON_DOCK = 12f;
    private List<Action> actions = new LinkedList<>();
    private MainWindow window;

    private static void loadLayouts(CControl globalPort) {
        try {
            if (LAYOUT_FILE.exists()) {
                globalPort.readXML(LAYOUT_FILE);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void installIcons(MainWindow mw) {
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
                new ImageIcon(IconFontSwing.buildImage(FontAwesomeSolid.EXTERNAL_LINK_ALT,
                        SIZE_ICON_DOCK, Color.black, Math.PI)));

        icons.setIcon("locationmanager.unmaximize_externalized", p,
                IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT, SIZE_ICON_DOCK));

        icons.setIcon("screen.maximize", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.EDIT, SIZE_ICON_DOCK));

        icons.setIcon("close", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_CLOSE, SIZE_ICON_DOCK));
    }

    private void ensureActions(MainWindow mw) {
        if (actions.isEmpty()) {
            int keypos = 0;
            for (String layout : LAYOUT_NAMES) {
                Integer key = keypos < LAYOUT_KEYS.length ? LAYOUT_KEYS[keypos] : null;
                actions.add(new LoadLayoutAction(mw, layout, key));
                actions.add(new SaveLayoutAction(mw, layout, key));
                keypos++;
            }
        }
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.window = window;
        installIcons(window);
        loadLayouts(window.getDockControl());
        setLayout(LAYOUT_NAMES[0]);
        window.getMediator().addGUIListener(new GUIListener() {
            @Override
            public void modalDialogOpened(EventObject e) {

            }

            @Override
            public void modalDialogClosed(EventObject e) {

            }

            @Override
            public void shutDown(EventObject e) {
                try {
                    window.getDockControl().writeXML(LAYOUT_FILE);
                } catch (IOException ex) {
                    ex.printStackTrace();
                }
            }
        });
    }

    private void setLayout(String layout) {
        CControl globalPort = window.getDockControl();
        boolean defaultLayoutDefined =
                Arrays.asList(globalPort.layouts()).contains(layout);
        if (defaultLayoutDefined) {
            globalPort.load(layout);
        }
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar toolBar = new JToolBar("Layout");
        JComboBox<String> comboLayouts = new JComboBox<>();

        class SaveAction extends MainWindowAction {

            protected SaveAction(MainWindow mainWindow) {
                super(mainWindow);
                setName("Save Layout");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                String name = Objects.requireNonNull(comboLayouts.getSelectedItem()).toString();
                mainWindow.getDockControl().save(name);
            }
        }

        class LoadAction extends MainWindowAction {

            protected LoadAction(MainWindow mainWindow) {
                super(mainWindow);
                setName("Load Layout");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                setLayout(Objects.requireNonNull(comboLayouts.getSelectedItem()).toString());
            }
        }

        toolBar.add(new JLabel("Layouts: "));
        for (String s : LAYOUT_NAMES) comboLayouts.addItem(s);
        toolBar.add(comboLayouts);
        toolBar.add(new LoadAction(mainWindow));
        toolBar.add(new SaveAction(mainWindow));
        return toolBar;
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        ensureActions(mainWindow);
        return actions;
    }
}


class SaveLayoutAction extends MainWindowAction {
    private final String layoutName;

    public SaveLayoutAction(MainWindow mainWindow, String name, Integer key) {
        super(mainWindow);
        this.layoutName = name;
        setName("Save Layout: " + name);
        setMenuPath("View.Layout.Save");
        if (key != null) {
            setAcceleratorKey(KeyStroke.getKeyStroke(key,
                    InputEvent.CTRL_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK));
        }
        KeyStrokeManager.lookupAndOverride(this,
                getClass().getName() + "$" + layoutName);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.getDockControl().save(layoutName);
        mainWindow.setStatusLine("Layout save at " + layoutName);
    }
}

class LoadLayoutAction extends MainWindowAction {
    private final String layoutName;

    public LoadLayoutAction(MainWindow mainWindow, String name, Integer key) {
        super(mainWindow);
        this.layoutName = name;
        setName("Load Layout: " + name);
        if (key != null) {
            setAcceleratorKey(KeyStroke.getKeyStroke(key, InputEvent.CTRL_DOWN_MASK));
        }
        KeyStrokeManager.lookupAndOverride(this,
                getClass().getName() + "$" + layoutName);
        setMenuPath("View.Layout.Load");
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
