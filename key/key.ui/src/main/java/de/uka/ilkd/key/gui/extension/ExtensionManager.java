package de.uka.ilkd.key.gui.extension;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.impl.Extension;
import de.uka.ilkd.key.gui.extension.impl.ExtensionSettings;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.KeYIcons;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.TablePanel;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import net.miginfocom.layout.CC;

import javax.swing.*;
import java.awt.*;
import java.util.*;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class ExtensionManager extends TablePanel implements SettingsProvider {
    private static final ExtensionSettings EXTENSION_SETTINGS = new ExtensionSettings();
    private HashMap<JCheckBox, Extension> map;

    public static ExtensionSettings getExtensionSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(EXTENSION_SETTINGS);
        return EXTENSION_SETTINGS;
    }

    private String keywords = "";

    public ExtensionManager() {
        refresh();
    }

    private void refresh() {
        removeAll();
        map = new HashMap<>();
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
            JCheckBox box = new JCheckBox();
            box.setText(it.getName());
            box.setSelected(!it.isDisabled());
            box.setEnabled(it.isOptional());
            map.put(box, it);

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
        Set<String> seq = new HashSet<>();
        map.forEach((k, v) -> {
            if (!k.isSelected()) {
                seq.add(v.getType().getName());
            }
        });
        ExtensionManager.getExtensionSettings().setForbiddenClasses(seq);
    }
}
