/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.Objects;
import java.util.ServiceLoader;
import javax.swing.*;

import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

public class KeYFileChooserLoadingOptions extends JPanel {
    private final JLabel lblProfile = new JLabel("Profile:");
    private final JComboBox<String> cboProfile = new JComboBox<>();

    public KeYFileChooserLoadingOptions(KeYFileChooser chooser) {
        setLayout(new MigLayout(new LC().fillX(), new AC().growPrio(10, 2)));

        var items = ServiceLoader.load(DefaultProfileResolver.class)
                .stream().map(it -> it.get().getProfileName())
                .toArray(String[]::new);
        cboProfile.setModel(new DefaultComboBoxModel<>(items));
        cboProfile.setSelectedItem(AbstractProfile.getDefaultProfile().name());

        lblProfile.setLabelFor(cboProfile);
        add(lblProfile);
        add(cboProfile);
    }

    public Profile getSelectedProfile() {
        var selected = getSelectedProfileName();
        var items = ServiceLoader.load(DefaultProfileResolver.class)
                .stream().filter(it -> Objects.equals(selected, it.get().getProfileName()))
                .findFirst();
        return items.map(it -> it.get().getDefaultProfile())
                .orElse(null);
    }

    public String getSelectedProfileName() {
        return (String) cboProfile.getSelectedItem();
    }
}
