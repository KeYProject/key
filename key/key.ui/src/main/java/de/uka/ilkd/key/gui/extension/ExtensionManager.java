package de.uka.ilkd.key.gui.extension;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.impl.Extension;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class ExtensionManager extends JPanel implements SettingsProvider {
    private Box boxList = new Box(BoxLayout.Y_AXIS);

    public ExtensionManager() {
        setLayout(new BorderLayout());
        add(new JLabel("Extension Settings"), BorderLayout.NORTH);
        add(new JScrollPane(boxList));
    }

    private void refresh() {
        boxList.removeAll();
        KeYGuiExtensionFacade.getExtensions().forEach(it ->
                boxList.add(new JCheckBox(new ExtensionActivationAction(it)))
        );
    }

    @Override
    public String getDescription() {
        return "Extensions";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        refresh();
        return this;
    }


    @Override
    public void applySettings(MainWindow window) {
    }

    private class ExtensionActivationAction extends KeyAction {
        public ExtensionActivationAction(Extension it) {
            setName(it.getName());
            setSelected(!it.isDisabled());
            setEnabled(it.isOptional());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            System.out.println("ExtensionActivationAction.actionPerformed");
        }
    }
}
