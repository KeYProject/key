/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.scene.Node;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextArea;
import javafx.scene.control.Toggle;
import javafx.scene.control.ToggleGroup;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.ShortcutSettingsF;
import de.uka.ilkd.key.gui.fx.theme.Theme;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * Settings provider for the appearance and behaviour of the UI, counter-part of
 * {@code de.uka.ilkd.key.gui.settings.StandardUISettings} of the Swing module {@code key.ui}.
 * <p>
 * It reads and writes the core {@link ViewSettings} and {@link GeneralSettings} (untouched code
 * in {@code key.core}, shared with the Swing UI). The Swing look-and-feel selector does not
 * carry over: the JavaFX UI has the two themes of the {@link ThemeManager} instead, selectable
 * here (applied immediately, like the Swing theme concept). The font size and font factor
 * settings are persisted like in Swing but apply to newly created views (the FX views pick the
 * fonts up at construction; a live resize facade is deferred — see the M4 report).
 * <p>
 * The children are the colors and the keyboard shortcuts panels, mirroring the Swing
 * {@code getChildren()} (renamed to {@link #getChildProviders()} here, see
 * {@link SettingsProviderF}).
 */
public class StandardUISettingsF extends SettingsPanelF implements SettingsProviderF {

    private static final String INFO_CLUTTER_RULESET =
        "Comma separated list of rule set names, containing clutter rules.";
    private static final String INFO_CLUTTER_RULE = "Comma separated listof clutter rules, \n"
        + "which are rules with less priority in the taclet menu";
    private static final String INFO_THEME =
        "Light and dark theme of the JavaFX UI. The change is applied immediately to all open "
            + "windows.";
    private static final String INFO_FONT_SIZE =
        "Font size of the tree and sequent views. Applies to newly created views.";
    private static final String INFO_FONT_FACTOR =
        "Global scaling factor of the UI fonts. Applies to newly created views.";
    private static final String INFO_CLASSIC_TACLET_DIALOG = """
            Use the classic (pre-2026) dialog when completing an interactive taclet \
            application.
            Offered as a fallback for a migration period; the redesigned dialog is the \
            default.""";
    private static final String MINIMIZE_INTERACTION_TIP =
        "If not ticked, applying a taclet manually will require you to instantiate "
            + "all schema variables.";
    private static final String INFO_MAX_TOOLTIP_LINES = """
            Maximum size (line count) of the tooltips of applicable rules
            with schema variable instantiations displayed.
            In case of longer tooltips the instantiation will be suppressed.
            """;

    private final ToggleGroup themeGroup = new ToggleGroup();
    /**
     * The child providers, created once: the tree, the initialization and the apply process must
     * share the same instances (a per-call creation would apply fresh, unpopulated panels).
     */
    private final java.util.List<SettingsProviderF> childProviders =
        java.util.List.of(new ColorSettingsProviderF(), new ShortcutSettingsF());
    private RadioButton lightRadio;
    private RadioButton darkRadio;
    private Spinner<Double> spFontSizeGlobal;
    private ComboBox<String> spFontSizeTreeSequent;
    private Spinner<Integer> txtMaxTooltipLines;
    private CheckBox chkShowLoadExamplesDialog;
    private CheckBox chkConfirmExit;
    private Spinner<Integer> spAutoSaveProof;
    private ComboBox<String> notificationAfterMacro;
    private CheckBox chkPrettyPrint;
    private CheckBox chkUseUnicode;
    private CheckBox chkSyntaxHighlightning;
    private CheckBox chkHidePackagePrefix;
    private CheckBox chkRightClickMacros;
    private CheckBox chkShowWholeTacletCB;
    private CheckBox chkShowUninstantiatedTaclet;
    private TextArea txtClutterRules;
    private TextArea txtClutterRuleSets;
    private CheckBox chkMinimizeInteraction;
    private CheckBox chkEnsureSourceConsistency;
    private CheckBox chkUseClassicTacletDialog;

    /** Creates the provider and builds the form once (the panel is reused). */
    public StandardUISettingsF() {
        setHeaderText(getDescription());

        addSeparator("General");

        lightRadio = new RadioButton("Light");
        darkRadio = new RadioButton("Dark");
        lightRadio.setToggleGroup(themeGroup);
        darkRadio.setToggleGroup(themeGroup);
        lightRadio.setUserData(Theme.LIGHT);
        darkRadio.setUserData(Theme.DARK);
        addRowWithHelp(INFO_THEME, new Label("Theme:"), lightRadio, darkRadio);
        spFontSizeGlobal = addDoubleNumberField("Global font factor", 0.1, 5, 0.1, 1.0,
            INFO_FONT_FACTOR, emptyValidator());
        String[] sizes = java.util.Arrays.stream(ConfigF.SIZES)
                .boxed().map(it -> it + " pt").toArray(String[]::new);
        spFontSizeTreeSequent = addComboBox("Tree and sequent font size", INFO_FONT_SIZE, sizes);
        txtMaxTooltipLines = addIntNumberField("Maximum line number for tooltips", 1, 100, 5, 40,
            INFO_MAX_TOOLTIP_LINES, emptyValidator());
        chkShowLoadExamplesDialog =
            addCheckBox("Show load examples dialog on startup", "", true);
        chkConfirmExit = addCheckBox("Confirm program exit", "", false);
        spAutoSaveProof =
            addIntNumberField("Auto save proof", 0, 10000000, 1000, 0, "", emptyValidator());
        notificationAfterMacro = addComboBox("Notification after macro finished", "",
            ViewSettings.NOTIFICATION_ALWAYS, ViewSettings.NOTIFICATION_UNFOCUSED,
            ViewSettings.NOTIFICATION_NEVER);

        addSeparator("Sequent View");
        chkPrettyPrint = addCheckBox("Pretty print terms", "", false);
        chkUseUnicode = addCheckBox("Use unicode", "", false);
        chkSyntaxHighlightning = addCheckBox("Use syntax highlighting", "", false);
        chkHidePackagePrefix = addCheckBox("Hide package prefix", "", false);
        chkRightClickMacros = addCheckBox("Right click for proof macros", "", false);

        addSeparator("Interaction");
        chkShowWholeTacletCB = addCheckBox("Show whole taclet",
            "Pretty-print whole Taclet including 'name', 'find', 'varCond' and 'heuristics'\n"
                + "(applies to tooltips in context menu)",
            false);
        chkShowUninstantiatedTaclet =
            addCheckBox("Show uninstantiated taclet", "recommended for unexperienced users",
                false);
        txtClutterRules = addTextArea("Clutter rules", "", INFO_CLUTTER_RULE, emptyValidator(), 4);
        txtClutterRuleSets =
            addTextArea("Clutter Rulesets", "", INFO_CLUTTER_RULESET, emptyValidator(), 4);
        chkMinimizeInteraction = addCheckBox("Minimise interactions", MINIMIZE_INTERACTION_TIP,
            false);
        chkEnsureSourceConsistency = addCheckBox("Ensure source consistency", "", true);
        chkUseClassicTacletDialog = addCheckBox("Use classic taclet instantiation dialog",
            INFO_CLASSIC_TACLET_DIALOG, false);

        refreshFromSettings();
    }

    @Override
    public String getDescription() {
        return "Appearance & Behaviour";
    }

    @Override
    public java.util.List<SettingsProviderF> getChildProviders() {
        return childProviders;
    }

    @Override
    public Node getPanel(MainWindowF window) {
        refreshFromSettings();
        return this;
    }

    /**
     * Re-reads the current settings into the input components (Swing
     * {@code StandardUISettings.getPanel}).
     */
    private void refreshFromSettings() {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings generalSettings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        txtClutterRules.setText(vs.clutterRules().value().replace(',', '\n'));
        txtClutterRuleSets.setText(vs.clutterRuleSets().value().replace(',', '\n'));

        Toggle themeToggle = ThemeManager.getInstance().getTheme() == Theme.DARK ? darkRadio
                : lightRadio;
        themeToggle.setSelected(true);

        spFontSizeGlobal.getValueFactory().setValue(vs.getUIFontSizeFactor());
        spFontSizeTreeSequent.getSelectionModel().select(vs.sizeIndex());
        txtMaxTooltipLines.getValueFactory().setValue(vs.getMaxTooltipLines());
        chkShowLoadExamplesDialog.setSelected(vs.getShowLoadExamplesDialog());
        chkShowWholeTacletCB.setSelected(vs.getShowWholeTaclet());
        chkShowUninstantiatedTaclet.setSelected(vs.getShowUninstantiatedTaclet());
        chkHidePackagePrefix.setSelected(vs.isHidePackagePrefix());
        chkPrettyPrint.setSelected(vs.isUsePretty());
        chkUseUnicode.setSelected(vs.isUseUnicode());
        chkSyntaxHighlightning.setSelected(vs.isUseSyntaxHighlighting());
        chkEnsureSourceConsistency.setSelected(generalSettings.isEnsureSourceConsistency());
        chkRightClickMacros.setSelected(generalSettings.isRightClickMacro());
        chkConfirmExit.setSelected(vs.confirmExit());
        spAutoSaveProof.getValueFactory().setValue(generalSettings.autoSavePeriod());
        chkMinimizeInteraction.setSelected(generalSettings.getTacletFilter());
        chkUseClassicTacletDialog.setSelected(vs.isUseClassicTacletDialog());
        notificationAfterMacro.getSelectionModel().select(vs.notificationAfterMacro());
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        vs.setUIFontSizeFactor(spFontSizeGlobal.getValue());
        vs.setMaxTooltipLines(txtMaxTooltipLines.getValue());
        vs.setShowLoadExamplesDialog(chkShowLoadExamplesDialog.isSelected());
        vs.setShowWholeTaclet(chkShowWholeTacletCB.isSelected());
        vs.setShowUninstantiatedTaclet(chkShowUninstantiatedTaclet.isSelected());
        vs.setHidePackagePrefix(chkHidePackagePrefix.isSelected());
        vs.setUsePretty(chkPrettyPrint.isSelected());
        vs.setUseUnicode(chkUseUnicode.isSelected());
        vs.setUseSyntaxHighlighting(chkSyntaxHighlightning.isSelected());
        gs.setEnsureSourceConsistency(chkEnsureSourceConsistency.isSelected());
        gs.setRightClickMacros(chkRightClickMacros.isSelected());
        vs.setConfirmExit(chkConfirmExit.isSelected());
        gs.setAutoSave(spAutoSaveProof.getValue());
        gs.setTacletFilter(chkMinimizeInteraction.isSelected());
        vs.setUseClassicTacletDialog(chkUseClassicTacletDialog.isSelected());
        vs.setFontIndex(spFontSizeTreeSequent.getSelectionModel().getSelectedIndex());
        String notification = notificationAfterMacro.getSelectionModel().getSelectedItem();
        if (notification != null) {
            vs.setNotificationAfterMacro(notification);
        }
        vs.clutterRules().parseFrom(txtClutterRules.getText().replace('\n', ','));
        vs.clutterRuleSets().parseFrom(txtClutterRuleSets.getText().replace('\n', ','));

        // theme switch applies immediately (the Swing look and feel needs a restart instead)
        Toggle themeToggle = themeGroup.getSelectedToggle();
        if (themeToggle != null) {
            ThemeManager.getInstance().setTheme((Theme) themeToggle.getUserData());
        }
        // the Swing original additionally rescales the fonts (FontSizeFacade) and fires
        // Config.DEFAULT.fireConfigChange(); the FX views pick font changes up when they are
        // (re)created, so no equivalent call exists yet
    }

    @Override
    public int getPriorityOfSettings() {
        return Integer.MIN_VALUE;
    }
}
