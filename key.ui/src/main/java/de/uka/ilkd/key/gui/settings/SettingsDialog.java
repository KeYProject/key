/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The settings dialog.
 *
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 * @see SettingsUi
 */
public class SettingsDialog extends JDialog {
    private static final long serialVersionUID = -3204453471778351602L;
    private static final Logger LOGGER = LoggerFactory.getLogger(SettingsDialog.class);

    private final MainWindow mainWindow;
    private final SettingsUi ui;
    private final Action actionCancel = new CancelAction();
    private final Action actionAccept = new AcceptAction();
    private final Action actionApply = new ApplyAction();
    private List<SettingsProvider> providers;

    public SettingsDialog(MainWindow owner) {
        super(owner, Dialog.ModalityType.TOOLKIT_MODAL);
        setTitle("Settings");

        mainWindow = owner;
        ui = new SettingsUi(owner, this);

        JPanel root = new JPanel(new BorderLayout());
        root.add(ui);
        JPanel buttonBar = createButtonBar();
        root.add(buttonBar, BorderLayout.SOUTH);
        setContentPane(root);

        getRootPane().registerKeyboardAction(e -> dispose(),
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);

        setSize(new Dimension(900, 600));
    }

    private JPanel createButtonBar() {
        JPanel p = new JPanel(new FlowLayout(FlowLayout.RIGHT));
        JButton btnCancel = new JButton(actionCancel);
        JButton btnApply = new JButton(actionApply);
        JButton btnAccept = new JButton(actionAccept);
        p.add(btnAccept);
        p.add(btnApply);
        p.add(btnCancel);
        return p;
    }

    public void setSettingsProvider(List<SettingsProvider> providers) {
        this.providers = providers;
        int width = this.ui.setSettingsProvider(providers);
        setSize(new Dimension(width, 600));
    }

    SettingsUi getUi() {
        return ui;
    }

    private List<Exception> apply() {
        List<Exception> exc = new LinkedList<>();
        apply(providers, exc);
        return exc;
    }

    private void apply(List<SettingsProvider> providers, List<Exception> exceptions) {
        for (SettingsProvider it : providers) {
            try {
                it.applySettings(mainWindow);
                apply(it.getChildren(), exceptions);
            } catch (Exception e) {
                exceptions.add(e);
            }
        }
    }

    private boolean showErrors(List<Exception> apply) {
        if (!apply.isEmpty()) {
            for (Exception e : apply) {
                LOGGER.error("", e);
            }
            String msg = apply.stream().map(Throwable::getMessage)
                    .collect(Collectors.joining("<br>", "<html>", "</html>"));
            JOptionPane.showMessageDialog(this, msg, "Error in Settings",
                JOptionPane.ERROR_MESSAGE);
            return false;
        }
        return true;
    }

    private class CancelAction extends KeyAction {
        private static final long serialVersionUID = -7590820300477946158L;

        public CancelAction() {
            setName("Cancel");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setVisible(false);
        }
    }

    private class AcceptAction extends KeyAction {
        private static final long serialVersionUID = -4975054687458772222L;

        public AcceptAction() {
            setName("OK");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setVisible(!showErrors(apply()));
        }
    }

    private class ApplyAction extends KeyAction {
        private static final long serialVersionUID = 3732950785908678379L;

        public ApplyAction() {
            setName("Apply");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            showErrors(apply());
        }
    }
}
