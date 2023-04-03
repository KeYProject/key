package de.uka.ilkd.key.gui.docking;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.settings.PathConfig;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.util.IconManager;
import bibliothek.gui.dock.util.Priority;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extension for working with layouts.
 *
 * @author Alexander Weigl
 * @version 1 (15.05.19)
 */
@KeYGuiExtension.Info(name = "Docking Helpers", optional = false, experimental = false,
    priority = 1)
public final class DockingLayout implements KeYGuiExtension, KeYGuiExtension.Startup,
        KeYGuiExtension.MainMenu, KeYGuiExtension.Toolbar {
    private static final Logger LOGGER = LoggerFactory.getLogger(DockingLayout.class);

    public static final float SIZE_ICON_DOCK = 12f;
    public static final File LAYOUT_FILE = new File(PathConfig.getKeyConfigDir(), "layout.xml");

    public static final String[] LAYOUT_NAMES = new String[] { "Default", "Slot 1", "Slot 2" };
    public static final int[] LAYOUT_KEYS = new int[] { KeyEvent.VK_F11, KeyEvent.VK_F12 };

    private final List<Action> actions = new LinkedList<>();
    private MainWindow window;

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

    private static void loadLayouts(CControl globalPort) {
        try {
            if (LAYOUT_FILE.exists()) {
                globalPort.readXML(LAYOUT_FILE);
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to load layouts", e);
        }
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
                    LOGGER.warn("Failed to save layouts", ex);
                }
            }
        });
    }

    private void setLayout(String layout) {
        CControl globalPort = window.getDockControl();
        boolean defaultLayoutDefined = Arrays.asList(globalPort.layouts()).contains(layout);
        if (defaultLayoutDefined) {
            globalPort.load(layout);
            DockingHelper.restoreMissingPanels(window);
        }
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar toolBar = new JToolBar("Docking Layout");
        JComboBox<String> comboLayouts = new JComboBox<>();

        class SaveAction extends MainWindowAction {
            private static final long serialVersionUID = -2688272657370615595L;

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
            private static final long serialVersionUID = 3130337190207622893L;

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
        for (String s : LAYOUT_NAMES) {
            comboLayouts.addItem(s);
        }
        toolBar.add(comboLayouts);
        toolBar.add(new LoadAction(mainWindow));
        toolBar.add(new SaveAction(mainWindow));
        toolBar.addSeparator();
        toolBar.add(new ResetLayoutAction(mainWindow));
        return toolBar;
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        ensureActions(mainWindow);
        return actions;
    }
}


class SaveLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = -2646217961498111734L;
    private final String layoutName;

    public SaveLayoutAction(MainWindow mainWindow, String name, Integer key) {
        super(mainWindow);
        this.layoutName = name;
        setName("Save as " + name);
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setMenuPath("View.Layout.Save");
        if (key != null) {
            setAcceleratorKey(KeyStroke.getKeyStroke(key,
                InputEvent.CTRL_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK));
        }
        KeyStrokeManager.lookupAndOverride(this, getClass().getName() + "$" + layoutName);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.getDockControl().save(layoutName);
        mainWindow.setStatusLine("Save layout as " + layoutName);
    }
}


class LoadLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = 3378477658914832831L;
    private final String layoutName;

    public LoadLayoutAction(MainWindow mainWindow, String name, Integer key) {
        super(mainWindow);
        this.layoutName = name;
        setName("Load " + name);
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        if (key != null) {
            setAcceleratorKey(KeyStroke.getKeyStroke(key, InputEvent.CTRL_DOWN_MASK));
        }
        KeyStrokeManager.lookupAndOverride(this, getClass().getName() + "$" + layoutName);
        setMenuPath("View.Layout.Load");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean defaultLayoutDefined =
            Arrays.asList(mainWindow.getDockControl().layouts()).contains(layoutName);
        if (defaultLayoutDefined) {
            mainWindow.getDockControl().load(layoutName);
            mainWindow.setStatusLine("Layout " + layoutName + " loaded");
        } else {
            mainWindow.setStatusLine("Layout " + layoutName + " could not be found.");
        }
    }
}


class ResetLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = 8772915552504055750L;

    public ResetLayoutAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Reset Layout");
        KeyStrokeManager.lookupAndOverride(this);
        setPriority(-1);
        setMenuPath("View.Layout");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        DockingHelper.restoreFactoryDefault(mainWindow);
        mainWindow.setStatusLine("Factory reset of the layout.");
    }
}
