/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.ArrayList;
import java.util.Map;
import java.util.ServiceLoader;
import javax.swing.*;

import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.Configuration;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.jspecify.annotations.NonNull;

public class KeYFileChooserLoadingOptions extends JPanel {
    private final JLabel lblProfile = new JLabel("Profile:");
    private final JComboBox<ProfileWrapper> cboProfile = new JComboBox<>();
    private final JLabel lblHelperProfile = SettingsPanel.createHelpLabel(
        """
                A Profile determines the proof environment, especially, the used built-in rules, specification repository, and taclet options.\s
                \s
                The default is "Java Profile".
                """);

    private final JTextArea lblProfileInfo = new JTextArea();

    private final JCheckBox lblSingleJava = new JCheckBox("Ignore other Java files");

    private final JLabel lblHelperSingleJava = SettingsPanel.createHelpLabel(
        """
                 Normally, KeY loads all Java files in the same folder and sub-folder of your selected file.\s
                 Mark this checkbox to only load the selected Java file.
                """);

    private final Map<Profile, KeYGuiExtension.OptionPanel> additionalOptionPanels =
        KeYGuiExtensionFacade.createAdditionalOptionPanels();


    private KeYGuiExtension.@Nullable OptionPanel currentOptionPanel = null;

    public KeYFileChooserLoadingOptions(KeYFileChooser chooser) {
        setLayout(new MigLayout(new LC().fillX().wrapAfter(3).maxWidth("400"),
            new AC().growPrio(10, 1).align("right", 0)));

        lblProfileInfo.setEditable(false);
        lblProfileInfo.setWrapStyleWord(true);
        lblProfileInfo.setLineWrap(true);

        var profiles =
            new ArrayList<>(ServiceLoader.load(DefaultProfileResolver.class)
                    .stream().map(it -> it.get().getDefaultProfile())
                    .map(ProfileWrapper::new)
                    .toList());

        final var legacyMode = new ProfileWrapper("Respect profile given in file", "",
            "Usable on KeY file which defines \\profile inside the file. " +
                "If no KeY file is loaded, falls back to legacy behavior",
            null);

        profiles.addFirst(legacyMode);

        var items = profiles.toArray(ProfileWrapper[]::new);

        cboProfile.setModel(new DefaultComboBoxModel<>(items));
        cboProfile.setSelectedItem(legacyMode);

        cboProfile.addItemListener(evt -> updateProfileInfo());
        updateProfileInfo();

        lblProfile.setLabelFor(cboProfile);
        add(lblProfile);
        add(cboProfile);
        add(lblHelperProfile);

        add(lblProfileInfo, new CC().newline("1").skip().span(2).growX());

        add(lblSingleJava, new CC().newline("2").skip());
        add(lblHelperSingleJava);
    }

    private void updateProfileInfo() {
        updateProfileInfo((ProfileWrapper) cboProfile.getSelectedItem());
    }

    private void updateProfileInfo(@Nullable ProfileWrapper selectedItem) {
        if (currentOptionPanel != null) {
            currentOptionPanel.deinstall(this);
        }

        if (selectedItem == null) {
            lblProfileInfo.setText("");
        } else {
            lblProfileInfo.setText(selectedItem.description());
            if (additionalOptionPanels.containsKey(selectedItem.profile)) {
                currentOptionPanel = additionalOptionPanels.get(selectedItem.profile);
                currentOptionPanel.install(this);
            }
        }
    }

    public @Nullable Profile getSelectedProfile() {
        var selected = (ProfileWrapper) cboProfile.getSelectedItem();
        if (selected == null) {
            return null;
        }
        return selected.profile();
    }

    public @Nullable Configuration getAdditionalProfileOptions() {
        if (currentOptionPanel == null) {
            return null;
        }
        return currentOptionPanel.getResult();
    }

    public @Nullable String getSelectedProfileName() {
        final var selectedItem = (ProfileWrapper) cboProfile.getSelectedItem();
        if (selectedItem == null)
            return null;
        return selectedItem.ident();
    }

    public boolean isOnlyLoadSingleJavaFile() {
        return lblSingleJava.isSelected();
    }

    record ProfileWrapper(String name, String ident, String description,
            @Nullable Profile profile) {
        ProfileWrapper(Profile profile) {
            this(profile.displayName(), profile.ident(), profile.description(), profile);
        }

        @Override
        public @NonNull String toString() {
            return name;
        }
    }
}
