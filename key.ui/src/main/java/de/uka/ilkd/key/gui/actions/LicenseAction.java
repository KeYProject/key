/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Shows the license dialog.
 * <p>
 * Shows the license of KeY (defined in LICENSE.txt) and of dependencies (THIRD_PARTY_LICENSES.txt).
 *
 * @author weigl
 */
public class LicenseAction extends MainWindowAction {
    public static final String KEY_FALLBACK =
        (KeYConstants.COPYRIGHT + "\nKeY is protected by the " + "GNU General Public License v2");

    private static final long serialVersionUID = 5606343347731759150L;

    public LicenseAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("License");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showLicense();
    }

    private JComponent createLicenseViewer(String s) {
        JTextArea text = new JTextArea(s, 20, 40);
        text.setEditable(false);
        text.setCaretPosition(0);
        JScrollPane scroll = new JScrollPane(text);
        return scroll;
    }

    private String readStream(URL resource, String fallback) {
        StringBuilder sb = new StringBuilder();
        try {
            InputStreamReader inp =
                new InputStreamReader(resource.openStream(), StandardCharsets.UTF_8);
            int c;
            char[] buf = new char[1024];
            while ((c = inp.read(buf)) > 0) {
                sb.append(buf, 0, c);
            }
            inp.close();
        } catch (IOException ioe) {
            return fallback;
        }
        return sb.toString();
    }

    public void showLicense() {
        URL lic = KeYResourceManager.getManager().getResourceFile(MainWindow.class, "LICENSE.TXT");

        URL thirdPartyLic = KeYResourceManager.getManager().getResourceFile(MainWindow.class,
            "THIRD_PARTY_LICENSES.txt");

        JDialog fr = new JDialog(mainWindow, "KeY License");
        fr.getContentPane().setLayout(new BorderLayout());
        JTabbedPane pane = new JTabbedPane();
        fr.add(pane);

        pane.addTab("KeY License", createLicenseViewer(readStream(lic, KEY_FALLBACK)));
        pane.addTab("Third party libraries", createLicenseViewer(readStream(thirdPartyLic, "")));

        JButton okButton = new JButton("OK");
        okButton.addActionListener(
            e -> ((JDialog) ((JButton) e.getSource()).getTopLevelAncestor()).dispose());
        fr.getContentPane().add(okButton, BorderLayout.SOUTH);
        fr.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        fr.setSize(600, 900);
        fr.setLocationRelativeTo(mainWindow);
        fr.setVisible(true);
    }

}
