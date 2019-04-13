package de.uka.ilkd.key.gui.extension;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.impl.Extension;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.KeYIcons;
import de.uka.ilkd.key.gui.settings.DefaultSettingsProvider;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.TablePanel;
import net.miginfocom.layout.CC;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class ExtensionManager extends TablePanel implements SettingsProvider {
    private String keywords = "";

    public ExtensionManager() {
        refresh();
    }

    private void refresh() {
        removeAll();
        keywords = "";

        JLabel lblHead = new JLabel("Extension Settings");
        keywords += lblHead.getText();
        lblHead.setFont(lblHead.getFont().deriveFont(16f));
        add(lblHead, new CC().span().alignX("left"));

        JLabel lblInfo = new JLabel("Settings will be applied on next restart");
        keywords += lblInfo.getText();
        lblInfo.setIcon(KeYIcons.WARNING_INCOMPLETE.getIcon());
        lblInfo.setBackground(Color.orange.darker());
        lblHead.setFont(lblHead.getFont().deriveFont(16f));
        add(lblInfo, new CC().span().alignX("left"));


        KeYGuiExtensionFacade.getExtensions().forEach(it -> {
            JCheckBox box = new JCheckBox(new ExtensionActivationAction(it));
            keywords += box.getText();
            add(new JLabel(), new CC().newline());
            add(box);

            JLabel lblProvides = new JLabel(getSupportLabel(it));
            keywords += lblProvides.getText();
            lblProvides.setFont(lblProvides.getFont().deriveFont(Font.ITALIC));
            add(new JLabel(), new CC().newline());
            add(lblProvides);

            if (!it.getDescription().isEmpty()) {
                add(new JLabel(), new CC().newline());
                add(createInfoArea(it.getDescription()));
                keywords += it.getDescription();
            }
        });
    }

    private String getSupportLabel(Extension it) {
        return "Provides: " +
                (it.supportsContextMenu() ? "ContextMenu " : "") +
                (it.supportsLeftPanel() ? "LeftPanel " : "") +
                (it.supportsMainMenu() ? "MainMenu " : "") +
                (it.supportsSettings() ? "Settings " : "") +
                (it.supportsStatusLine() ? "StatusLine " : "") +
                (it.supportsToolbar() ? "Toolbar " : "");
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
    public boolean contains(String substring) {
        return keywords.toLowerCase().contains(substring.toLowerCase());
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
