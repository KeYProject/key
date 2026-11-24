/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.screenshot;

import java.awt.image.BufferedImage;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.image.PixelReader;
import javafx.scene.image.WritableImage;
import javafx.scene.layout.VBox;
import javafx.stage.PopupWindow;
import javafx.stage.Window;
import javax.imageio.ImageIO;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The theme gallery of the visual QA affordance ({@code key.fx.screenshot=&lt;dir&gt;}): renders
 * the live UI in-process through {@link Node#snapshot} (synchronous, so every PNG shows exactly
 * the CSS state at capture time) and saves the PNGs — no screen capture and no pointer
 * interaction. Like the {@code key.fx.verify.*} harnesses this class lives in the test source set
 * and is invoked reflectively from {@code MainWindowF} (inert without the property, the
 * {@code run} task carries the test outputs on the runtime classpath).
 * <p>
 * The gallery captures: one full-window PNG per AtlantaFX theme (the {@link ThemeManager} switch
 * is the real menu/settings path), the View menu popup with the Theme submenu open (the picker
 * with its radio items, opened through the popup content — see {@link #openSubmenu}) and the
 * settings dialog with the theme combo (the Standard UI panel). The gallery waits for the
 * demo-load toast to dismiss and re-selects {@link Theme#PRIMER_LIGHT} for the picker and dialog
 * shots, so the gallery files are reproducible.
 */
public final class ScreenshotVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ScreenshotVerifyF.class);

    private ScreenshotVerifyF() {
    }

    /**
     * Starts the gallery on a background worker (the caller runs on the FX thread; the worker
     * hops back for every scene access through {@link FxUtil#runAndWait}).
     *
     * @param mainWindow the main window
     * @return the start report for the status line
     */
    public static String run(MainWindowF mainWindow) {
        String dir = System.getProperty("key.fx.screenshot", "build/ui-screenshots");
        Thread worker = new Thread(() -> gallery(mainWindow, Path.of(dir)), "screenshot-gallery");
        worker.setDaemon(true);
        worker.start();
        return "screenshot gallery started";
    }

    /** Renders the theme gallery into {@code dir} (runs on the background worker thread). */
    private static void gallery(MainWindowF mainWindow, Path dir) {
        try {
            Files.createDirectories(dir);
            Scene scene = mainWindow.getStage().getScene();
            // wait for the demo-load toast (queued through Platform.runLater by the load
            // callback) to appear and to auto-dismiss, so all gallery shots are uniform
            for (int i = 0; i < 60 && NotificationManagerF.getInstance()
                    .getVisibleToastCount() == 0; i++) {
                Thread.sleep(250);
            }
            for (int i = 0; i < 48 && NotificationManagerF.getInstance()
                    .getVisibleToastCount() > 0; i++) {
                Thread.sleep(250);
            }
            // 1) one full-window PNG per theme — the switch goes through the real ThemeManager
            // setTheme (the View > Theme menu and the settings combo route through the same
            // choke point); the settle time lets the user-agent stylesheet swap and the CSS
            // pass settle before the synchronous snapshot
            int index = 1;
            for (Theme theme : Theme.values()) {
                FxUtil.runAndWait(() -> ThemeManager.getInstance().setTheme(theme));
                Thread.sleep(900);
                Path file = dir.resolve(String.format("%02d-%s.png", index, fileName(theme)));
                FxUtil.runAndWait(() -> snapshot(scene.getRoot(), file));
                index++;
            }
            // 2) the View menu popup with the Theme submenu open (the picker) — on Primer Light
            // for the docs
            FxUtil.runAndWait(() -> ThemeManager.getInstance().setTheme(Theme.PRIMER_LIGHT));
            Thread.sleep(900);
            Menu view = findMenuBar(scene.getRoot()).getMenus().stream()
                    .filter(menu -> "View".equals(mnemonic(menu.getText()))).findFirst()
                    .orElseThrow();
            Menu themeMenu = findSubmenu(view, "Theme");
            FxUtil.runAndWait(view::show);
            Thread.sleep(600);
            Path viewPopupFile = dir.resolve("menu-view.png");
            FxUtil.runAndWait(() -> snapshot(newestPopup().getScene().getRoot(), viewPopupFile));
            FxUtil.runAndWait(() -> openSubmenu(view, themeMenu));
            Thread.sleep(600);
            Path themePopupFile = dir.resolve("menu-theme.png");
            FxUtil.runAndWait(() -> snapshot(newestPopup().getScene().getRoot(), themePopupFile));
            FxUtil.runAndWait(view::hide);
            // 3) the settings dialog with the theme combo (the Standard UI panel is selected, so
            // the combo shows; dialog.show() is not blocking, the stage is closed after the
            // snapshot)
            FxUtil.runAndWait(() -> SettingsManagerF.getInstance()
                    .showSettingsDialog(mainWindow, SettingsManagerF.STANDARD_UI_SETTINGS));
            Thread.sleep(1500);
            Path dialogFile = dir.resolve("settings.png");
            FxUtil.runAndWait(
                () -> snapshot(newestDialog().getScene().getRoot(), dialogFile));
            FxUtil.runAndWait(() -> newestDialog().hide());
            int count;
            try (var pngs = Files.list(dir)) {
                count = (int) pngs.filter(file -> file.toString().endsWith(".png")).count();
            }
            LOGGER.info("Screenshot gallery complete: {} PNG files in {}", count, dir);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            LOGGER.error("Screenshot gallery interrupted", e);
        } catch (Exception e) {
            LOGGER.error("Screenshot gallery failed", e);
        }
    }

    /** @return the lowercase dashed file name fragment of a theme (e.g. {@code nord-dark}) */
    private static String fileName(Theme theme) {
        return theme.name().toLowerCase().replace('_', '-');
    }

    /** @return the newest popup window (the menu popups show one after the other) */
    private static PopupWindow newestPopup() {
        List<Window> windows =
            Window.getWindows().stream().filter(w -> w instanceof PopupWindow).toList();
        return (PopupWindow) windows.get(windows.size() - 1);
    }

    /**
     * @return the first node of the internal popup content class ({@code ContextMenuContent}) in
     *         the given subtree — the popup scene root is a plain pane with the content nested
     *         inside — or {@code null} if the subtree has none
     */
    private static Node findContent(Node node) {
        if (node.getClass().getName().endsWith("ContextMenuContent")) {
            return node;
        }
        if (node instanceof Parent parent) {
            for (Node child : parent.getChildrenUnmodifiable()) {
                Node found = findContent(child);
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    /** @return the newest non-popup window (the settings dialog was created last) */
    private static Window newestDialog() {
        List<Window> windows = Window.getWindows().stream()
                .filter(w -> !(w instanceof PopupWindow)).toList();
        return windows.get(windows.size() - 1);
    }

    /**
     * Opens the submenu inside the showing parent popup the way the skin does it: the popup
     * content opens submenus only from its own interaction handlers ({@link Menu#show()} merely
     * flips the showing flag and nothing listens to it for nested menus), so the call goes
     * through the internal popup content class ({@code com.sun.javafx.scene.control
     * .ContextMenuContent}): it selects the row of the submenu (the highlighted row matches the
     * hover look) and calls the private {@code showSubmenu(Menu)}. The reflective call needs
     * {@code --add-opens javafx.controls/com.sun.javafx.scene.control=ALL-UNNAMED}; without the
     * flag it falls back to {@link Menu#show()}, which does not open a popup window.
     */
    private static void openSubmenu(Menu parent, Menu submenu) {
        try {
            Node content = findContent(newestPopup().getScene().getRoot());
            if (content == null) {
                LOGGER.warn("No popup content in the popup scene: falling back to Menu.show");
                submenu.show();
                return;
            }
            Class<?> cls = content.getClass();
            VBox itemsContainer = (VBox) cls.getMethod("getItemsContainer").invoke(content);
            // select the row of the submenu: the selected row is the anchor of the submenu
            // popup (a missing selection makes the skin silently skip the show) — looked up by
            // label, else by the item index (the rows map 1:1 to the items as long as the menu
            // has no scroll arrows, like the View menu)
            int index = -1;
            try {
                java.lang.reflect.Method labelAt = cls.getMethod("getLabelAt", int.class);
                String text = mnemonic(submenu.getText());
                for (int i = 0; i < itemsContainer.getChildren().size(); i++) {
                    try {
                        Label label = (Label) labelAt.invoke(content, i);
                        if (label != null && text.equals(mnemonic(label.getText()))) {
                            index = i;
                            break;
                        }
                    } catch (RuntimeException e) {
                        LOGGER.debug("Row {} of the popup has no label", i, e);
                    }
                }
            } catch (ReflectiveOperationException | RuntimeException e) {
                LOGGER.debug("Label lookup of the popup rows failed", e);
            }
            if (index < 0) {
                index = parent.getItems().indexOf(submenu);
            }
            LOGGER.info("Selecting popup row {} of {} for the submenu", index,
                itemsContainer.getChildren().size());
            cls.getMethod("requestFocusOnIndex", int.class).invoke(content, index);
            java.lang.reflect.Method showSubmenu = cls.getDeclaredMethod("showSubmenu", Menu.class);
            showSubmenu.setAccessible(true);
            showSubmenu.invoke(content, submenu);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Opening the submenu through the popup content failed; falling back to "
                + "Menu.show (pass --add-opens "
                + "javafx.controls/com.sun.javafx.scene.control=ALL-UNNAMED)", e);
            submenu.show();
        }
    }

    /**
     * @return the first {@link MenuBar} below the given parent node (menus are no {@link Node}s,
     *         so they are looked up through {@link MenuBar#getMenus()} instead of a traversal)
     */
    private static MenuBar findMenuBar(Parent parent) {
        for (Node child : parent.getChildrenUnmodifiable()) {
            if (child instanceof MenuBar menuBar) {
                return menuBar;
            }
            if (child instanceof Parent nested) {
                MenuBar found = findMenuBar(nested);
                if (found != null) {
                    return found;
                }
            }
        }
        throw new IllegalStateException("No menu bar in the scene graph");
    }

    /** @return the first submenu with the given text below the given parent menu */
    private static Menu findSubmenu(Menu parent, String text) {
        for (javafx.scene.control.MenuItem item : parent.getItems()) {
            if (item instanceof Menu menu && text.equals(mnemonic(menu.getText()))) {
                return menu;
            }
        }
        throw new IllegalStateException("No submenu '" + text + "' in " + parent.getText());
    }

    /** @return the menu text without the mnemonic underscore (e.g. {@code _View} → {@code View}) */
    private static String mnemonic(String text) {
        return text == null ? "" : text.replace("_", "");
    }

    /**
     * Snapshots a node into the PNG file (toolkit-free saving: the pixels are copied into a
     * {@link BufferedImage} and written by {@link ImageIO}; the {@code javafx.swing} module with
     * {@code SwingFXUtils} is deliberately not a dependency of key.ui.fx). {@link Node#snapshot}
     * with a {@code null} callback is synchronous and runs on the FX thread — unlike
     * {@link Scene#snapshot}, whose callback fires asynchronously (the captured frame would then
     * race subsequent scene changes).
     */
    private static void snapshot(Node node, Path file) {
        try {
            WritableImage image = node.snapshot(null, null);
            saveImage(image, file);
            LOGGER.info("Screenshot: {}", file);
        } catch (Exception e) {
            throw new IllegalStateException("Snapshot " + file + " failed", e);
        }
    }

    /** Copies the image pixels into a {@link BufferedImage} and writes the PNG file. */
    private static void saveImage(WritableImage image, Path file) throws Exception {
        PixelReader reader = image.getPixelReader();
        int width = (int) image.getWidth();
        int height = (int) image.getHeight();
        BufferedImage buffered = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
        for (int y = 0; y < height; y++) {
            for (int x = 0; x < width; x++) {
                buffered.setRGB(x, y, reader.getArgb(x, y));
            }
        }
        Files.createDirectories(file.getParent());
        ImageIO.write(buffered, "png", file.toFile());
    }
}
