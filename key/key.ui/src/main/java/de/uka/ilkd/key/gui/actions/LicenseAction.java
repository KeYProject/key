// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;

/**
 * Shows the license dialog.
 * <p>
 * Shows the license of KeY (defined in LICENSE.txt) and of dependencies (THIRD_PARTY_LICENSES.txt).
 *
 * @author weigl
 */
public class LicenseAction extends MainWindowAction {
    public static final String KEY_FALLBACK = (KeYConstants.COPYRIGHT + "\nKeY is protected by the "
            + "GNU General Public License v2");

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
        StringBuffer sb = new StringBuffer();
        try {
            InputStreamReader inp = new InputStreamReader(resource.openStream(), "UTF-8");
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
        URL lic = KeYResourceManager.getManager().getResourceFile(MainWindow.class,
                "LICENSE.TXT");

        URL thirdPartyLic = KeYResourceManager.getManager().getResourceFile(MainWindow.class,
                "THIRD_PARTY_LICENSES.txt");

        JDialog fr = new JDialog(mainWindow, "KeY License");
        fr.getContentPane().setLayout(new BorderLayout());
        JTabbedPane pane = new JTabbedPane();
        fr.add(pane);

        pane.addTab("KeY License", createLicenseViewer(readStream(lic, KEY_FALLBACK)));
        pane.addTab("Third party libraries", createLicenseViewer(readStream(thirdPartyLic, "")));

        JButton ok = new JButton("OK");
        ok.addActionListener(e -> ((JDialog) ((JButton) e.getSource())
                .getTopLevelAncestor()).dispose());
        fr.getContentPane().add(ok, BorderLayout.SOUTH);
        fr.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        fr.setSize(600, 900);
        fr.setLocationRelativeTo(null);
        fr.setVisible(true);
    }

}