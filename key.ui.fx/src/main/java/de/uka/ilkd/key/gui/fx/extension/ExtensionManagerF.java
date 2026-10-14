/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import javafx.scene.Node;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

/**
 * The "Extension Settings" panel of the settings dialog (Swing {@code ExtensionManager},
 * key.ui/extension/ExtensionManager.java:33-150, registered by Swing SettingsManager.java:62):
 * a checkbox per discovered FX extension. Unchecked extensions are persisted as forbidden class
 * names ({@link ExtensionSettingsF}, the same "Extensions"/"disabled" section the Swing app
 * uses) and contribute nothing after the next restart —
 * {@link KeYGuiExtensionFacadeF#contributingExtensions() the contribution filter}. Optional
 * extensions can be unchecked; mandatory ones are displayed with a disabled checkbox (Swing
 * {@code box.setEnabled(it.isOptional())}, ExtensionManager.java:68). Experimental extensions
 * are marked with the flask icon (Swing adds {@code IconFactory.EXPERIMENTAL_EXTENSION},
 * ExtensionManager.java:74-76); Swing additionally keeps them off until their feature is
 * activated ({@code Extension.isDisabled}, Extension.java:57-63), which the FX port does not
 * enforce — the checkboxes here reflect exactly what the FX app applies.
 * <p>
 * Swing's help button per extension ({@code createHelpButton}, ExtensionManager.java:97-101) is
 * not ported: it only appears for extension classes carrying the Swing {@code @HelpInfo}
 * annotation, and no FX extension class does.
 */
public final class ExtensionManagerF extends SettingsPanelF implements SettingsProviderF {

    /** the tree entry (Swing {@code getDescription}, ExtensionManager.java:121-123) */
    private static final String DESCRIPTION = "Extensions";

    /** the panel title (Swing {@code setHeaderText}, ExtensionManager.java:39) */
    private static final String HEADER = "Extension Settings";

    /** the panel subtitle (Swing {@code setSubHeaderText}, ExtensionManager.java:40) */
    private static final String SUB_HEADER = "Settings will be applied on next restart";

    /**
     * the experimental-mode explanation (Swing {@code lblExplainExperimental},
     * ExtensionManager.java:45-47)
     */
    private static final String EXPERIMENTAL_NOTE =
        "The flask marks extensions that are only available, if KeY was started in "
            + "experimental mode. Restart KeY with `--experimental`.";

    /** the checkbox state (Swing {@code map}, ExtensionManager.java:35) */
    private final Map<CheckBox, Class<? extends KeYGuiExtensionF>> checkboxToExtension =
        new HashMap<>();

    public ExtensionManagerF() {
        setHeaderText(HEADER);
        setSubHeaderText(SUB_HEADER);
        refresh();
    }

    @Override
    public String getDescription() {
        return DESCRIPTION;
    }

    @Override
    public Node getPanel(MainWindowF window) {
        refresh();
        return this;
    }

    /**
     * Rebuilds the extension rows (Swing {@code refresh}, ExtensionManager.java:59-102): the
     * extensions sorted optional-first (Swing {@code comparingInt}, ExtensionManager.java:63-65;
     * the maintainer-disabled filter has no FX counterpart since the FX
     * {@link KeYGuiExtensionF.Info Info} carries no {@code disabled} flag), each with its
     * checkbox, the flask marker, the provides line and the description.
     */
    private void refresh() {
        checkboxToExtension.clear();
        pCenter.getChildren().clear();
        // the experimental-mode explanation (Swing lblExplainExperimental, :45-49)
        Label note = new Label(EXPERIMENTAL_NOTE);
        note.setWrapText(true);
        note.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.EXPERIMENTAL_EXTENSION));
        addRowWithHelp("", new Label(), note);
        KeYGuiExtensionFacadeF.getExtensions().stream()
                .sorted(Comparator
                        .comparingInt(extension -> KeYGuiExtensionFacadeF.isOptionalOf(extension)
                                ? 0
                                : 1))
                .forEach(this::addExtensionRow);
    }

    /**
     * Adds the rows of one extension (Swing ExtensionManager.java:66-101): the checkbox row
     * (preceded by the flask icon for experimental extensions like the Swing icon cell), the
     * italic provides line and the description.
     */
    private void addExtensionRow(KeYGuiExtensionF extension) {
        Class<? extends KeYGuiExtensionF> type = extension.getClass();
        CheckBox box = new CheckBox(KeYGuiExtensionFacadeF.nameOf(extension));
        box.setSelected(!KeYGuiExtensionFacadeF.getExtensionSettings().getForbiddenClasses()
                .contains(type.getName()));
        box.setDisable(!KeYGuiExtensionFacadeF.isOptionalOf(extension));
        checkboxToExtension.put(box, type);

        HBox checkboxRow = new HBox(6);
        if (KeYGuiExtensionFacadeF.isExperimentalOf(extension)) {
            checkboxRow.getChildren()
                    .add(IconFactoryF.createIcon(IconFactoryF.Key.EXPERIMENTAL_EXTENSION));
        }
        checkboxRow.getChildren().add(box);
        addRowWithHelp("", new Label(), checkboxRow);

        Label provides = new Label(providesLabel(extension));
        provides.setStyle("-fx-font-style: italic;");
        addRowWithHelp("", new Label(), provides);

        String description = KeYGuiExtensionFacadeF.descriptionOf(extension);
        if (!description.isEmpty()) {
            Label descriptionLabel = new Label(description);
            descriptionLabel.setWrapText(true);
            addRowWithHelp("", new Label(), descriptionLabel);
        }
    }

    /**
     * @return the provides line listing the implemented capabilities (Swing
     *         {@code getSupportLabel}, ExtensionManager.java:104-112 — the same six
     *         capabilities; the FX-only tooltip and shortcut capabilities stay unlisted like in
     *         the Swing original)
     */
    private static String providesLabel(KeYGuiExtensionF extension) {
        return "Provides: " + (extension instanceof KeYGuiExtensionF.ContextMenuF ? "ContextMenu "
                : "")
            + (extension instanceof KeYGuiExtensionF.LeftPanelF ? "LeftPanel " : "")
            + (extension instanceof KeYGuiExtensionF.MainMenuF ? "MainMenu " : "")
            + (extension instanceof KeYGuiExtensionF.SettingsF ? "Settings " : "")
            + (extension instanceof KeYGuiExtensionF.StatusLineF ? "StatusLine " : "")
            + (extension instanceof KeYGuiExtensionF.ToolbarF ? "Toolbar " : "");
    }

    @Override
    public boolean contains(String substring) {
        if (substring == null || substring.isEmpty()) {
            return false;
        }
        // the search keywords cover the extension names, provides lines and descriptions (Swing
        // keyword accumulation, ExtensionManager.java:61-100)
        StringBuilder keywords =
            new StringBuilder(DESCRIPTION).append(HEADER).append(SUB_HEADER);
        for (KeYGuiExtensionF extension : KeYGuiExtensionFacadeF.getExtensions()) {
            keywords.append(KeYGuiExtensionFacadeF.nameOf(extension))
                    .append(providesLabel(extension))
                    .append(KeYGuiExtensionFacadeF.descriptionOf(extension));
        }
        return keywords.toString().toLowerCase().contains(substring.toLowerCase());
    }

    @Override
    public void apply(MainWindowF window) {
        // the unchecked class names become forbidden (Swing applySettings,
        // ExtensionManager.java:139-148)
        Set<String> seq = new HashSet<>();
        checkboxToExtension.forEach((box, type) -> {
            if (!box.isSelected()) {
                seq.add(type.getName());
            }
        });
        KeYGuiExtensionFacadeF.getExtensionSettings().setForbiddenClasses(seq);
    }
}
