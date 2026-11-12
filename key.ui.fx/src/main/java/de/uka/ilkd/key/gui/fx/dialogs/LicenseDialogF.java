/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.util.KeYConstants;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A5 (P3c): JavaFX port of the Swing {@code LicenseAction} dialog
 * (key.ui/.../gui/actions/LicenseAction.java), opened by the About&gt;License… entry
 * ({@code MainWindowF.showLicense}). The dialog shows the license of KeY (defined in
 * {@code LICENSE.TXT}) and of the dependencies ({@code THIRD_PARTY_LICENSES.txt}) in two tabs,
 * mirroring the Swing {@code JTabbedPane} layout.
 * <p>
 * Port notes and deviations from the Swing original:
 * <ul>
 * <li>The license texts live in {@code key.ui/src/main/resources/de/uka/ilkd/key/gui/}. They are
 * only <em>runtime</em> resources for key.ui.fx (key.ui itself stays off the compile classpath),
 * so they are read by their classpath resource path through the application class loader instead
 * of {@code KeYResourceManager.getResourceFile(MainWindow.class, …)}; when the file cannot be
 * loaded the Swing fallback text {@link #KEY_FALLBACK} is shown for the KeY license and an empty
 * text for the third-party tab.</li>
 * <li>Unlike the Swing ok-button-in-a-{@code BorderLayout} this port adds the button to a
 * {@code ButtonBar} at the bottom with the same behaviour (closing the dialog).</li>
 * </ul>
 */
public final class LicenseDialogF {
    private static final Logger LOGGER = LoggerFactory.getLogger(LicenseDialogF.class);

    /**
     * Fallback text shown when {@code LICENSE.TXT} cannot be loaded (Swing {@code KEY_FALLBACK}).
     */
    public static final String KEY_FALLBACK = (KeYConstants.COPYRIGHT + "\nKeY is protected by the "
        + "GNU General Public License v2, or (at your option) any later version");

    /** Classpath path of the KeY license text (resource lives in the key.ui module). */
    private static final String LICENSE_RESOURCE = "de/uka/ilkd/key/gui/LICENSE.TXT";

    /** Classpath path of the third-party licenses text (resource lives in the key.ui module). */
    private static final String THIRD_PARTY_RESOURCE =
        "de/uka/ilkd/key/gui/THIRD_PARTY_LICENSES.txt";

    private LicenseDialogF() {
    }

    /**
     * Shows the modal license dialog (Swing {@code LicenseAction.showLicense}): a
     * {@code TabPane} with the KeY license and the third-party licenses, plus an OK button.
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     */
    public static void show(Window owner) {
        javafx.stage.Stage dialog = new javafx.stage.Stage();
        dialog.setTitle("KeY License");
        dialog.initOwner(owner);
        if (owner != null) {
            // Swing: JDialog(mainWindow, "KeY License") — window-modal in front of the owner
            dialog.initModality(Modality.WINDOW_MODAL);
        }

        TabPane pane = new TabPane();
        // Swing: JTextArea(s, 20, 40) in a JScrollPane — read-only text with a scroll bar
        pane.getTabs().addAll(
            new Tab("KeY License", createLicenseViewer(readText(readResource(LICENSE_RESOURCE),
                KEY_FALLBACK))),
            new Tab("Third party libraries",
                createLicenseViewer(readText(readResource(THIRD_PARTY_RESOURCE), ""))));

        Button okButton = new Button("OK");
        okButton.setDefaultButton(true);
        okButton.setOnAction(e -> dialog.close());

        BorderPane root = new BorderPane();
        root.setCenter(pane);
        root.setBottom(okButton);
        BorderPane.setMargin(okButton, new Insets(10));
        Scene scene = new Scene(root, 600, 900);
        ThemeManager.getInstance().manage(scene);
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                dialog.close();
                e.consume();
            }
        });
        dialog.setScene(scene);
        dialog.showAndWait();
    }

    /** Swing {@code createLicenseViewer}: a read-only multi-line text area (top-aligned caret). */
    private static javafx.scene.Node createLicenseViewer(String text) {
        TextArea area = new TextArea(text);
        area.setEditable(false);
        area.positionCaret(0);
        return area;
    }

    /**
     * Looks up a license resource by its classpath path (see the class javadoc for why the
     * resources are addressed by path and not via {@code getResourceFile}).
     *
     * @param path the classpath resource path of the license text
     * @return the resource URL, or {@code null} when the license module is not on the classpath
     */
    private static @Nullable URL readResource(String path) {
        return LicenseDialogF.class.getClassLoader().getResource(path);
    }

    /**
     * Reads a resource URL to a string (Swing {@code LicenseAction.readStream}, 1024-char
     * buffer, UTF-8); on failure (or a {@code null} URL) the fallback text is returned.
     */
    private static String readText(URL resource, String fallback) {
        StringBuilder sb = new StringBuilder();
        try (InputStream in = resource.openStream();
                InputStreamReader inp = new InputStreamReader(in, StandardCharsets.UTF_8)) {
            char[] buf = new char[1024];
            int c;
            while ((c = inp.read(buf)) > 0) {
                sb.append(buf, 0, c);
            }
        } catch (IOException | NullPointerException ioe) {
            LOGGER.warn("License text resource {} not readable, using fallback", resource);
            return fallback;
        }
        return sb.toString();
    }
}
