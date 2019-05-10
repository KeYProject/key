package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import javax.swing.*;

/**
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class StandardUISettings extends SettingsPanel implements SettingsProvider {
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
    private final JSpinner spFontSizeTreeSequent;
    private final JCheckBox chkAllowProofBundleSaving;

    public StandardUISettings() {
        setHeaderText(getDescription());

        spFontSizeGlobal = createNumberTextField(new SpinnerNumberModel(1, 0.1, 5, 0.1),
                emptyValidator());
        addTitledComponent("Global font factor: ", spFontSizeGlobal, "");
        spFontSizeTreeSequent = createNumberTextField(new SpinnerNumberModel(1, 0.1, 5, 0.1),
                emptyValidator());
        addTitledComponent("Tree&Sequent font factor: ", spFontSizeTreeSequent, "");


        String info = "Maximum size (line count) of the tooltips of applicable rules\n"
                + "<br> with schema variable instantiations displayed.\n"
                + "In case of longer <br>tooltips the instantiation will be suppressed.\n";
        txtMaxTooltipLines = addNumberField("Maximum line number for tooltips",
                1, 100, 5, info, emptyValidator());

        chkShowWholeTacletCB = addCheckBox("Show whole taclet", "Pretty-print whole Taclet including \n" +
                "'name', 'find', 'varCond' and 'heuristics'", false, emptyValidator());

        chkShowUninstantiatedTaclet = addCheckBox("Show uninstantiated taclet", "recommended for unexperienced users",
                false, emptyValidator());

        chkPrettyPrint = addCheckBox("Pretty print terms", "", false, emptyValidator());
        chkUseUnicode = addCheckBox("Use unicode", "", false, emptyValidator());
        chkSyntaxHighlightning = addCheckBox("Use syntax highlightning", "", false, emptyValidator());
        chkHidePackagePrefix = addCheckBox("Hide package prefix", "", false, emptyValidator());
        chkConfirmExit = addCheckBox("Confirm program exit", "", false, emptyValidator());
        spAutoSaveProof = addNumberField("Auto save proof", 0, 10000000, 1000, "", emptyValidator());
        chkMinimizeInteraction = addCheckBox("Minimise Interactions", "", false, emptyValidator());
        chkAllowProofBundleSaving = addCheckBox("Allow Proof Bundle Saving", "", false, emptyValidator());
        chkRightClickMacros = addCheckBox("Right click for Macros", "", false, emptyValidator());
    }

    @Override
    public String getDescription() {
        return "Appearance & Behaviour";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings generalSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        spFontSizeGlobal.setValue(viewSettings.getUIFontSizeFactor());
        txtMaxTooltipLines.setValue(viewSettings.getMaxTooltipLines());
        chkShowWholeTacletCB.setSelected(viewSettings.getShowWholeTaclet());
        chkShowUninstantiatedTaclet.setSelected(viewSettings.getShowUninstantiatedTaclet());
        chkHidePackagePrefix.setSelected(viewSettings.isHidePackagePrefix());
        chkPrettyPrint.setSelected(viewSettings.isUsePretty());
        chkUseUnicode.setSelected(viewSettings.isUseUnicode());
        chkSyntaxHighlightning.setSelected(viewSettings.isUseSyntaxHighlighting());
        chkAllowProofBundleSaving.setSelected(generalSettings.isAllowBundleSaving());
        chkRightClickMacros.setSelected(generalSettings.isRightClickMacro());
        chkConfirmExit.setSelected(viewSettings.confirmExit());
        spAutoSaveProof.setValue(generalSettings.autoSavePeriod());
        chkMinimizeInteraction.setSelected(generalSettings.tacletFilter());
        spFontSizeTreeSequent.setValue(viewSettings.sizeIndex());

        return this;
    }

    @Override
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        vs.setUIFontSizeFactor((Double) spFontSizeGlobal.getValue());
        vs.setMaxTooltipLines((Integer) txtMaxTooltipLines.getValue());

        vs.setShowWholeTaclet(chkShowWholeTacletCB.isSelected());
        vs.setShowUninstantiatedTaclet(chkShowUninstantiatedTaclet.isSelected());
        vs.setHidePackagePrefix(chkHidePackagePrefix.isSelected());
        vs.setUsePretty(chkPrettyPrint.isSelected());
        vs.setUseUnicode(chkUseUnicode.isSelected());
        vs.setUseSyntaxHighlighting(chkSyntaxHighlightning.isSelected());
        gs.setAllowBundleSaving(chkAllowProofBundleSaving.isSelected());
        gs.setRightClickMacros(chkRightClickMacros.isSelected());
        vs.setConfirmExit(chkConfirmExit.isSelected());
        gs.setAutoSave((Integer) spAutoSaveProof.getValue());
        gs.setTacletFilter(chkMinimizeInteraction.isSelected());
        vs.setFontIndex((Integer) spFontSizeTreeSequent.getValue());
        FontSizeFacade.resizeFonts(vs.getUIFontSizeFactor());
    }
}
