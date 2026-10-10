/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.profileloading;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.ColumnConstraints;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.Configuration;

import org.jspecify.annotations.Nullable;

/**
 * Loading options collected before a proof load: the profile selection, the profile description
 * and the profile-specific additional option panels (currently the {@link WDLoadOptionPanelF}),
 * plus the "Ignore other Java files" checkbox.
 * <p>
 * smalldialogs: FX port of the Swing {@code de.uka.ilkd.key.gui.KeYFileChooserLoadingOptions}
 * ({@code KeYFileChooserLoadingOptions.java:37-113}), the loading-options accessory of the Swing
 * {@code KeYFileChooser} used by {@code OpenFileAction}.
 * <p>
 * <b>Placement deviation:</b> Swing embeds this panel <em>inside</em> the file chooser
 * ({@code KeYFileChooser.addLoadingOptions()}); JavaFX {@code FileChooser} has no accessory API,
 * so the identical content is collected in this modal pre-load dialog, shown from
 * {@code MainWindowF.openFileChooser} directly after a file has been picked. Cancel aborts the
 * load, mirroring Swing where the options cannot be confirmed without approving the chooser.
 * Like Swing (only {@code OpenFileAction} adds the accessory), the dialog is shown only in the
 * open-file flow — recent files, quick load and the demo load keep their behavior.
 * <p>
 * The Swing original collects the profile-specific option panels via the {@code KeYGuiExtension}
 * SPI ({@code KeYGuiExtensionFacade.createAdditionalOptionPanels()}, {@code
 * KeYFileChooserLoadingOptions.java:53-54}); the FX extension SPI does not exist yet, so the
 * panels are registered in the local {@link #additionalOptionPanels} map built from the ported
 * {@link WDLoadOptionPanelF#getProfile()} (the extension seam stays open). For the same reason
 * the profile list only contains the {@code DefaultProfileResolver} services on the
 * {@code key.ui.fx} classpath (Swing additionally offers the InfFlow profile of
 * {@code key.core.infflow}, which is not a dependency of {@code key.ui.fx}).
 */
public final class LoadingOptionsDialogF extends javafx.stage.Stage {

    /**
     * The loading options selected in the dialog, forwarded to the proof loader (Swing
     * {@code OpenFileAction.actionPerformed:70-76}).
     *
     * @param selectedProfile the profile to force on the new proofs, {@code null} for the legacy
     *        mode "Respect profile given in file" (Swing {@code ProfileWrapper} with a null
     *        profile → {@code forceNewProfileOfNewProofs(false)})
     * @param additionalProfileOptions the configuration of the selected profile's option panel,
     *        {@code null} if the profile has no option panel (Swing
     *        {@code getAdditionalProfileOptions()})
     * @param singleJavaFile whether to load only the selected Java file (Swing
     *        {@code isOnlyLoadSingleJavaFile()})
     */
    public record LoadOptions(@Nullable Profile selectedProfile,
            @Nullable Configuration additionalProfileOptions, boolean singleJavaFile) {
    }

    /**
     * Combo box entry (Swing record {@code ProfileWrapper}, {@code
     * KeYFileChooserLoadingOptions.java:141-151}): name, ident, description and the profile
     * itself ({@code null} for the legacy mode).
     */
    private record ProfileWrapper(String name, String ident, String description,
            @Nullable Profile profile) {
        ProfileWrapper(Profile profile) {
            this(profile.displayName(), profile.ident(), profile.description(), profile);
        }

        @Override
        public String toString() {
            return name;
        }
    }

    /** Swing {@code lblProfile}. */
    private final Label lblProfile = new Label("Profile:");

    /** Swing {@code cboProfile}. */
    private final ComboBox<ProfileWrapper> cboProfile = new ComboBox<>();

    /** Swing {@code lblProfileInfo}: the description of the selected profile. */
    private final TextArea lblProfileInfo = new TextArea();

    /** Swing {@code lblSingleJava}. */
    private final CheckBox lblSingleJava = new CheckBox("Ignore other Java files");

    /**
     * Host of the currently installed profile option panel (Swing {@code currentOptionPanel},
     * which is added to/removed from the accessory panel on profile changes).
     */
    private final VBox optionPanelHost = new VBox();

    /**
     * smalldialogs: the profile option panels. Swing fills this map via the
     * {@code KeYGuiExtension} SPI ({@code createAdditionalOptionPanels()}); here the ported WD
     * panel is registered directly (SPI seam open, see class javadoc).
     */
    private static final Map<Profile, WDLoadOptionPanelF> additionalOptionPanels =
        buildAdditionalOptionPanels();

    /** The dialog result; {@code null} until confirmed (Swing: chooser approved). */
    private @Nullable LoadOptions result;

    private LoadingOptionsDialogF(Window owner) {
        setTitle("Loading Options");
        if (owner != null) {
            initOwner(owner);
        }
        initModality(Modality.WINDOW_MODAL);

        // Swing KeYFileChooserLoadingOptions.java:60-70: the profiles of the
        // DefaultProfileResolver services, legacy mode first, legacy mode preselected
        List<ProfileWrapper> profiles = new ArrayList<>(ServiceLoader
                .load(DefaultProfileResolver.class)
                .stream().map(it -> it.get().getDefaultProfile()).map(ProfileWrapper::new)
                .toList());
        profiles.addFirst(new ProfileWrapper("Respect profile given in file", "",
            "Usable on KeY file which defines \\profile inside the file. "
                + "If no KeY file is loaded, falls back to legacy behavior",
            null));
        cboProfile.getItems().setAll(profiles);
        cboProfile.getSelectionModel().selectFirst();
        cboProfile.getSelectionModel().selectedItemProperty()
                .addListener((obs, old, selected) -> updateProfileInfo());

        // Swing lblProfileInfo: non-editable, word wrap
        lblProfileInfo.setEditable(false);
        lblProfileInfo.setWrapText(true);
        lblSingleJava.setTooltip(new Tooltip("""
                Normally, KeY loads all Java files in the same folder and sub-folder of your
                selected file. Mark this checkbox to only load the selected Java file."""));

        GridPane grid = new GridPane();
        grid.setHgap(8);
        grid.setVgap(8);
        grid.setPadding(new javafx.geometry.Insets(12));
        ColumnConstraints labels = new ColumnConstraints();
        ColumnConstraints inputs = new ColumnConstraints();
        inputs.setHgrow(Priority.ALWAYS);
        ColumnConstraints helps = new ColumnConstraints();
        grid.getColumnConstraints().setAll(labels, inputs, helps);
        lblProfile.setLabelFor(cboProfile);

        lblProfileInfo.setPrefColumnCount(1);
        lblProfileInfo.setPrefRowCount(3);

        grid.add(lblProfile, 0, 0);
        grid.add(cboProfile, 1, 0);
        grid.add(SettingsPanelF.createHelpLabel("""
                A Profile determines the proof environment, especially, the used built-in rules,
                specification repository, and taclet options.

                The default is "Java Profile".
                """), 2, 0);
        grid.add(lblProfileInfo, 1, 1, 2, 1);
        GridPane.setHgrow(lblProfileInfo, Priority.ALWAYS);
        grid.add(lblSingleJava, 0, 2, 2, 1);
        grid.add(optionPanelHost, 1, 3, 2, 1);

        updateProfileInfo();

        Button cancelButton = new Button("Cancel");
        cancelButton.setOnAction(e -> {
            result = null;
            close();
        });
        Button loadButton = new Button("Load");
        loadButton.setDefaultButton(true);
        loadButton.setOnAction(e -> {
            ProfileWrapper selected = cboProfile.getSelectionModel().getSelectedItem();
            Profile profile = selected == null ? null : selected.profile();
            WDLoadOptionPanelF panel = profile == null ? null : additionalOptionPanels.get(profile);
            result = new LoadOptions(profile, panel == null ? null : panel.getResult(),
                lblSingleJava.isSelected());
            close();
        });
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().addAll(cancelButton, loadButton);

        BorderPane root = new BorderPane(grid, null, null, buttonBar, null);
        Scene scene = new Scene(root, 520, 380);
        ThemeManager.getInstance().manage(scene);
        // Escape cancels (Swing: the options are lost with a canceled chooser dialog)
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == javafx.scene.input.KeyCode.ESCAPE) {
                cancelButton.fire();
                e.consume();
            }
        });
        setScene(scene);
        sizeToScene();
    }

    /**
     * Swing {@code updateProfileInfo} ({@code KeYFileChooserLoadingOptions.java:96-119}): shows
     * the description of the selected profile and installs the matching additional option panel
     * (Swing {@code install}/{@code deinstall} of {@code WDLoadDialogOptionPanel.java:85-104};
     * here install/remove becomes adding/removing the panel from {@link #optionPanelHost}).
     */
    private void updateProfileInfo() {
        // Swing: currentOptionPanel.deinstall(this) on profile change
        optionPanelHost.getChildren().clear();
        ProfileWrapper selected = cboProfile.getSelectionModel().getSelectedItem();
        if (selected == null) {
            lblProfileInfo.setText("");
        } else {
            lblProfileInfo.setText(selected.description());
            WDLoadOptionPanelF panel = additionalOptionPanels.get(selected.profile());
            if (panel != null) {
                optionPanelHost.getChildren().add(panel);
            }
        }
    }

    /**
     * Builds the profile option panel registry (Swing
     * {@code KeYGuiExtensionFacade.createAdditionalOptionPanels()}; the FX registry is
     * constructed from the ported {@link WDLoadOptionPanelF}, see the class javadoc).
     */
    private static Map<Profile, WDLoadOptionPanelF> buildAdditionalOptionPanels() {
        Map<Profile, WDLoadOptionPanelF> map = new LinkedHashMap<>();
        WDLoadOptionPanelF wdPanel = new WDLoadOptionPanelF();
        map.put(wdPanel.getProfile(), wdPanel);
        return map;
    }

    /**
     * Opens the dialog modally and waits for the user decision (Swing: the accessory is part of
     * the chooser dialog; the approval handling in {@code OpenFileAction.actionPerformed:70-76}
     * corresponds to the confirmed dialog).
     *
     * @param owner the owner window (the main window stage)
     * @return the selected loading options, or {@code null} if the dialog was canceled
     */
    public static @Nullable LoadOptions showOptions(Window owner) {
        LoadingOptionsDialogF dialog = new LoadingOptionsDialogF(owner);
        dialog.centerOnScreen();
        dialog.showAndWait();
        return dialog.result;
    }

    /**
     * The selected profile (Swing {@code getSelectedProfile()}, {@code
     * KeYFileChooserLoadingOptions.java:121-130}); {@code null} in legacy mode.
     *
     * @return the profile to force on the new proofs or {@code null}
     */
    public @Nullable Profile getSelectedProfile() {
        ProfileWrapper selected = cboProfile.getSelectionModel().getSelectedItem();
        return selected == null ? null : selected.profile();
    }

    /**
     * The options of the selected profile's option panel (Swing
     * {@code getAdditionalProfileOptions()}, {@code KeYFileChooserLoadingOptions.java:132-139});
     * {@code null} without an installed panel.
     *
     * @return the additional profile options or {@code null}
     */
    public @Nullable Configuration getAdditionalProfileOptions() {
        Profile profile = getSelectedProfile();
        if (profile == null) {
            return null;
        }
        WDLoadOptionPanelF panel = additionalOptionPanels.get(profile);
        return panel == null ? null : panel.getResult();
    }

    /**
     * Swing {@code isOnlyLoadSingleJavaFile} ({@code KeYFileChooserLoadingOptions.java:141-144}).
     *
     * @return whether to load only the selected Java file
     */
    public boolean isOnlyLoadSingleJavaFile() {
        return lblSingleJava.isSelected();
    }
}
