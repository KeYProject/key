package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import javax.swing.*;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class StandardUISettings extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = -7484169054465984605L;
    private static final String INFO_CLUTTER_RULESET =
            "Comma separated list of rule set names, containing clutter rules.";
    private static final String INFO_CLUTTER_RULE = "Comma separated listof clutter rules, \n" +
            "which are rules with less priority in the taclet menu";

    private final JSpinner spFontSizeGlobal;
    private final JSpinner txtMaxTooltipLines;
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
    private final JTextField txtClutterRules;
    private final JTextField txtClutterRuleSets;

    public StandardUISettings() {
        setHeaderText(getDescription());

        spFontSizeGlobal = createNumberTextField(new SpinnerNumberModel(1, 0.1, 5, 0.1),
                emptyValidator());
        addTitledComponent("Global font factor: ", spFontSizeGlobal, "");

        String[] sizes =
                Arrays.stream(Config.SIZES).boxed().map(it -> it + " pt").toArray(String[]::new);
        spFontSizeTreeSequent = this.<String>createSelection(sizes, emptyValidator());
        addTitledComponent("Tree and sequent font factor: ", spFontSizeTreeSequent, "");


        String info = "Maximum size (line count) of the tooltips of applicable rules\n"
                + "<br> with schema variable instantiations displayed.\n"
                + "In case of longer <br>tooltips the instantiation will be suppressed.\n";
        txtMaxTooltipLines = addNumberField("Maximum line number for tooltips",
                1, 100, 5, info, emptyValidator());

        chkShowWholeTacletCB =
                addCheckBox("Show whole taclet", "Pretty-print whole Taclet including \n" +
                            "'name', 'find', 'varCond' and 'heuristics'", false, emptyValidator());

        chkShowUninstantiatedTaclet =
                addCheckBox("Show uninstantiated taclet", "recommended for unexperienced users",
                            false, emptyValidator());

        txtClutterRules = addTextField("Clutter rules", "", INFO_CLUTTER_RULE, emptyValidator());
        txtClutterRuleSets =
                addTextField("Clutter Rulesets", "", INFO_CLUTTER_RULESET, emptyValidator());

        chkPrettyPrint = addCheckBox("Pretty print terms", "", false, emptyValidator());
        chkUseUnicode = addCheckBox("Use unicode", "", false, emptyValidator());
        chkSyntaxHighlightning =
                addCheckBox("Use syntax highlighting", "", false, emptyValidator());
        chkHidePackagePrefix = addCheckBox("Hide package prefix", "", false, emptyValidator());
        chkConfirmExit = addCheckBox("Confirm program exit", "", false, emptyValidator());
        spAutoSaveProof =
                addNumberField("Auto save proof", 0, 10000000, 1000, "", emptyValidator());
        chkMinimizeInteraction = addCheckBox("Minimise interactions", "", false, emptyValidator());
        chkEnsureSourceConsistency =
                addCheckBox("Ensure source consistency", "", true, emptyValidator());
        chkRightClickMacros =
                addCheckBox("Right click for proof macros", "", false, emptyValidator());
    }


    @Override
    public String getDescription() {
        return "Appearance & Behaviour";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings generalSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();


        txtClutterRules.setText(vs.clutterRules().value());
        txtClutterRuleSets.setText(vs.clutterRuleSets().value());

        spFontSizeGlobal.setValue(vs.getUIFontSizeFactor());
        txtMaxTooltipLines.setValue(vs.getMaxTooltipLines());
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
        chkMinimizeInteraction.setSelected(generalSettings.tacletFilter());
        spFontSizeTreeSequent.setSelectedIndex(vs.sizeIndex());

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

        vs.setUIFontSizeFactor((Double) spFontSizeGlobal.getValue());
        vs.setMaxTooltipLines((Integer) txtMaxTooltipLines.getValue());

        vs.clutterRules().set(txtClutterRules.getText());
        vs.clutterRuleSets().set(txtClutterRuleSets.getText());


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
        vs.setFontIndex((Integer) spFontSizeTreeSequent.getSelectedIndex());
        FontSizeFacade.resizeFonts(vs.getUIFontSizeFactor());
    }

    @Override
    public int getPriorityOfSettings() {
        return Integer.MIN_VALUE;
    }
}
