/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.util.Arrays;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MinimizeInteraction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import com.formdev.flatlaf.FlatDarculaLaf;
import com.formdev.flatlaf.FlatDarkLaf;
import com.formdev.flatlaf.FlatIntelliJLaf;
import com.formdev.flatlaf.FlatLightLaf;
import com.formdev.flatlaf.themes.FlatMacDarkLaf;
import com.formdev.flatlaf.themes.FlatMacLightLaf;

/**
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class StandardUISettings extends SettingsPanel implements SettingsProvider {
    private static final String INFO_CLUTTER_RULESET =
        "Comma separated list of rule set names, containing clutter rules.";
    private static final String INFO_CLUTTER_RULE = "Comma separated listof clutter rules, \n"
        + "which are rules with less priority in the taclet menu";
    private static final String LOOK_AND_FEEL_INFO = """
            Look and feel used by KeY.
            'System' tries to mimic the default looks, 'Metal' is the Java default.
            KeY must be restarted to apply changes.""";

    static {
        FlatLightLaf.installLafInfo();
        FlatIntelliJLaf.installLafInfo();
        FlatMacLightLaf.installLafInfo();
        FlatDarkLaf.installLafInfo();
        FlatDarculaLaf.installLafInfo();
        FlatMacDarkLaf.installLafInfo();
    }


    /**
     * Labels for the selectable look and feels. Must be kept in sync with {@link #LAF_CLASSES}.
     */
    private static final List<String> LAF_LABELS =
        Arrays.stream(UIManager.getInstalledLookAndFeels()).map(UIManager.LookAndFeelInfo::getName)
                .toList();


    /**
     * Classnames corresponding to the labels in {@link #LAF_LABELS}.
     */
    private static final List<String> LAF_CLASSES =
        Arrays.stream(UIManager.getInstalledLookAndFeels())
                .map(UIManager.LookAndFeelInfo::getClassName).toList();

    private final JComboBox<String> lookAndFeel;
    private final JSpinner spFontSizeGlobal;
    private final JSpinner txtMaxTooltipLines;
    private final JCheckBox chkShowLoadExamplesDialog;
    private final JCheckBox chkShowWholeTacletCB;
    private final JCheckBox chkShowUninstantiatedTaclet;
    private final JCheckBox chkRightClickMacros;
    private final JCheckBox chkPrettyPrint;
    private final JCheckBox chkUseUnicode;
    private final JCheckBox chkSyntaxHighlightning;
    private final JCheckBox chkHidePackagePrefix;
    private final JCheckBox chkConfirmExit;
    private final JSpinner spAutoSaveProof;
    private final JCheckBox chkMinimizeInteraction;
    private final JComboBox<String> spFontSizeTreeSequent;
    private final JCheckBox chkEnsureSourceConsistency;
    private final JTextArea txtClutterRules;
    private final JTextArea txtClutterRuleSets;
    private final JComboBox<String> notificationAfterMacro;

    public StandardUISettings() {
        setHeaderText(getDescription());

        addSeparator("General");
        lookAndFeel = createSelection(LAF_LABELS.toArray(new String[0]), emptyValidator());
        addTitledComponent("Look and feel", lookAndFeel, LOOK_AND_FEEL_INFO);

        spFontSizeGlobal =
            createNumberTextField(new SpinnerNumberModel(1, 0.1, 5, 0.1), emptyValidator());
        addTitledComponent("Global font factor", spFontSizeGlobal, "");

        String[] sizes =
            Arrays.stream(Config.SIZES).boxed().map(it -> it + " pt").toArray(String[]::new);
        spFontSizeTreeSequent = this.createSelection(sizes, emptyValidator());
        addTitledComponent("Tree and sequent font size", spFontSizeTreeSequent, "");


        String info = """
                Maximum size (line count) of the tooltips of applicable rules
                with schema variable instantiations displayed.
                In case of longer tooltips the instantiation will be suppressed.
                """;
        txtMaxTooltipLines =
            addNumberField("Maximum line number for tooltips", 1, 100, 5, info, emptyValidator());


        chkShowLoadExamplesDialog =
            addCheckBox("Show load examples dialog on startup", "", true, emptyValidator());

        chkConfirmExit = addCheckBox("Confirm program exit", "", false, emptyValidator());

        spAutoSaveProof =
            addNumberField("Auto save proof", 0, 10000000, 1000, "", emptyValidator());
        notificationAfterMacro = addComboBox("Notification after macro finished", "", 1,
            emptyValidator(), ViewSettings.NOTIFICATION_ALWAYS, ViewSettings.NOTIFICATION_UNFOCUSED,
            ViewSettings.NOTIFICATION_NEVER);

        addSeparator("Sequent View");
        chkPrettyPrint = addCheckBox("Pretty print terms", "", false, emptyValidator());
        chkUseUnicode = addCheckBox("Use unicode", "", false, emptyValidator());
        chkSyntaxHighlightning =
            addCheckBox("Use syntax highlighting", "", false, emptyValidator());
        chkHidePackagePrefix = addCheckBox("Hide package prefix", "", false, emptyValidator());
        chkRightClickMacros =
            addCheckBox("Right click for proof macros", "", false, emptyValidator());

        addSeparator("Interaction");
        chkShowWholeTacletCB = addCheckBox("Show whole taclet",
            "Pretty-print whole Taclet including 'name', 'find', 'varCond' and 'heuristics'\n(applies to tooltips in context menu)",
            false, emptyValidator());

        chkShowUninstantiatedTaclet = addCheckBox("Show uninstantiated taclet",
            "recommended for unexperienced users", false, emptyValidator());

        txtClutterRules = addTextArea("Clutter rules", "", INFO_CLUTTER_RULE, emptyValidator());

        txtClutterRuleSets =
            addTextArea("Clutter Rulesets", "", INFO_CLUTTER_RULESET, emptyValidator());

        chkMinimizeInteraction = addCheckBox("Minimise interactions", MinimizeInteraction.TOOL_TIP,
            false, emptyValidator());
        chkEnsureSourceConsistency =
            addCheckBox("Ensure source consistency", "", true, emptyValidator());
    }


    @Override
    public String getDescription() {
        return "Appearance & Behaviour";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings generalSettings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();


        txtClutterRules.setText(vs.clutterRules().value().replace(',', '\n'));
        txtClutterRuleSets.setText(vs.clutterRuleSets().value().replace(',', '\n'));

        for (int i = 0; i < LAF_CLASSES.size(); i++) {
            if (LAF_CLASSES.get(i).equals(vs.getLookAndFeel())) {
                lookAndFeel.setSelectedIndex(i);
                break;
            }
        }
        spFontSizeGlobal.setValue(vs.getUIFontSizeFactor());
        txtMaxTooltipLines.setValue(vs.getMaxTooltipLines());
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
        spAutoSaveProof.setValue(generalSettings.autoSavePeriod());
        chkMinimizeInteraction.setSelected(generalSettings.getTacletFilter());
        spFontSizeTreeSequent.setSelectedIndex(vs.sizeIndex());
        notificationAfterMacro.setSelectedItem(vs.notificationAfterMacro());

        return this;
    }

    @Override
    public List<SettingsProvider> getChildren() {
        return Arrays.asList(SettingsManager.COLOR_SETTINGS, SettingsManager.SHORTCUT_SETTINGS);
    }

    @Override
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        vs.setLookAndFeel(LAF_CLASSES.get(lookAndFeel.getSelectedIndex()));
        vs.setUIFontSizeFactor((Double) spFontSizeGlobal.getValue());
        vs.setMaxTooltipLines((Integer) txtMaxTooltipLines.getValue());

        vs.clutterRules().parseFrom(txtClutterRules.getText().replace('\n', ','));
        vs.clutterRuleSets().parseFrom(txtClutterRuleSets.getText().replace('\n', ','));

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
        gs.setAutoSave((Integer) spAutoSaveProof.getValue());
        gs.setTacletFilter(chkMinimizeInteraction.isSelected());
        vs.setFontIndex(spFontSizeTreeSequent.getSelectedIndex());
        vs.setNotificationAfterMacro((String) notificationAfterMacro.getSelectedItem());
        Config.DEFAULT.setDefaultFonts();
        FontSizeFacade.resizeFonts(vs.getUIFontSizeFactor());
        Config.DEFAULT.fireConfigChange();
    }

    @Override
    public int getPriorityOfSettings() {
        return Integer.MIN_VALUE;
    }
}
