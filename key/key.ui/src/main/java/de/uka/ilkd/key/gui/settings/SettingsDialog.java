package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsDialog extends JDialog {
    private final MainWindow mainWindow;
    private final SettingsUi ui;
    private Action actionCancel = new CancelAction();
    private Action actionAccept = new AcceptAction();
    private Action actionApply = new ApplyAction();
    private List<SettingsProvider> providers;

    public SettingsDialog(MainWindow owner) {
        super(owner, Dialog.ModalityType.TOOLKIT_MODAL);
        setTitle("Settings");

        mainWindow = owner;
        ui = new SettingsUi(owner);

        JPanel root = new JPanel(new BorderLayout());
        root.add(ui);
        JPanel buttonBar = createButtonBar();
        root.add(buttonBar, BorderLayout.SOUTH);
        setContentPane(root);
        setSize(600, 400);
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
        this.ui.setSettingsProvider(providers);
    }

    SettingsUi getUi() {
        return ui;
    }

    private class CancelAction extends KeyAction {
        public CancelAction() {
            setName("Cancel");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setVisible(false);
        }
    }

    private class AcceptAction extends KeyAction {
        public AcceptAction() {
            setName("Accept");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            actionApply.actionPerformed(e);
            setVisible(false);
        }
    }

    private class ApplyAction extends KeyAction {
        public ApplyAction() {
            setName("Apply");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            providers.forEach(it -> it.applySettings(mainWindow));
        }
    }
}
