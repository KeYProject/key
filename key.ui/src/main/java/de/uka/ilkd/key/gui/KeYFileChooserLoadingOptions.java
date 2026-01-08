package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.util.Objects;
import java.util.ServiceLoader;

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
