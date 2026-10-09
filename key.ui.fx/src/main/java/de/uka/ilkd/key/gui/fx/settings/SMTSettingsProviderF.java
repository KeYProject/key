/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.LinkedHashMap;
import java.util.Map;
import javafx.scene.Node;
import javafx.scene.control.CheckBox;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

/**
 * Settings provider for the SMT solvers, counter-part of
 * {@code de.uka.ilkd.key.gui.smt.settings.SMTSettingsProvider} of the Swing module
 * {@code key.ui} (registered there as {@code SettingsManager.SMT_SETTINGS}, the target of the
 * Options | SMT Solvers… action).
 * <p>
 * The panel shows one check box per available solver (from the pure-Java
 * {@link SolverTypes#getSolverTypes()}, key.core) and the SMT options that persist 1:1 on
 * {@link ProofIndependentSMTSettings}. All values are read in {@link #getPanel(MainWindowF)}
 * from {@link ProofIndependentSettings#DEFAULT_INSTANCE} and written back in
 * {@link #apply(MainWindowF)}, like the Swing original's {@code getPanel} (clone)/{@code
 * applySettings} ({@code settings.copy}) pair, SMTSettingsProvider.java:172-183.
 */
public class SMTSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    /**
     * One check box per solver type, in the {@code SolverTypes.getSolverTypes()} order.
     * <p>
     * menu: MP4 — the checks mirror the solver selection of the settings
     * ({@code ProofIndependentSMTSettings.containsSolver}), the selection state is persisted as
     * the active solver name ({@code setActiveSolver}, the setter the Swing SMT toolbar writes
     * via {@code setActiveSolverUnion} → {@code setActiveSolver},
     * ProofIndependentSMTSettings.java:475-480): there is no add/remove API for the
     * {@code solverTypes} collection, so a deselected box cannot remove the solver from the
     * settings list (KNOWN-DEFERRED, see {@link #apply(MainWindowF)}).
     */
    private final Map<SolverType, CheckBox> solverChecks = new LinkedHashMap<>();

    /** menu: MP4 — 1:1 persisted toggle (Swing property {@code SHOW_SMT_RES_DIA}). */
    private CheckBox chkShowResultsAfterExecution;

    /**
     * menu: MP4 — 1:1 persisted toggle (Swing property {@code PROP_STORE_SMT_TRANSLATION_FILE}).
     */
    private CheckBox chkStoreSMTTranslationToFile;

    /**
     * menu: MP4 — 1:1 persisted toggle (Swing property {@code PROP_STORE_TACLET_TRANSLATION_FILE}).
     */
    private CheckBox chkStoreTacletTranslationToFile;

    /**
     * menu: MP4 — 1:1 persisted toggle (Swing property {@code SOLVER_ENABLED_ON_LOAD}; the
     * "Enable SMT solvers when loading proofs" check of the Swing provider,
     * SMTSettingsProvider.java:238-242).
     */
    private CheckBox chkEnableOnLoad;

    /** Creates the provider and builds the form once (the panel is reused). */
    public SMTSettingsProviderF() {
        setHeaderText(getDescription());

        // menu: MP4 — SolverTypes.getSolverTypes() is pure Java (key.core, service-loaded
        // solver properties), the check states come from the settings in getPanel.
        addSeparator("SMT Solvers");
        for (SolverType type : SolverTypes.getSolverTypes()) {
            solverChecks.put(type, addCheckBox(type.getName(), "", false));
        }

        addSeparator("SMT Options");
        chkShowResultsAfterExecution =
            addCheckBox("Show results after execution", "", false);
        chkStoreSMTTranslationToFile = addCheckBox("Store SMT translation to file", "", false);
        chkStoreTacletTranslationToFile =
            addCheckBox("Store taclet translation to file", "", false);
        chkEnableOnLoad = addCheckBox("Enable SMT solvers when loading proofs", "", true);

        // menu: KNOWN-DEFERRED — the remaining Swing options of SMTSettingsProvider /
        // SolverOptions are not ported: the per-solver command/parameters/timeout and support
        // panels (SolverOptions.java:36-50), the progress-dialog mode, the global timeout, the
        // concurrent-process count, the int/seq/object/locset bounds, the "check for support"
        // toggle and the store-translation file path panel (SMTSettingsProvider.java:105-158,
        // 185-256). The four persisted toggles above and the solver selection are the
        // functional core; the rest is left for the SMT milestone.

        refreshFromSettings();
    }

    @Override
    public String getDescription() {
        return "SMT";
    }

    @Override
    public Node getPanel(MainWindowF window) {
        // like the Swing original, re-read the current settings on every getPanel
        // (SMTSettingsProvider.java:172-176 prepares a clone there; here the same values are
        // read directly and the write-back happens in apply).
        refreshFromSettings();
        return this;
    }

    /**
     * Re-reads the current settings into the input components (Swing
     * {@code setSmtSettings}, SMTSettingsProvider.java:258-271).
     */
    private void refreshFromSettings() {
        ProofIndependentSMTSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        for (Map.Entry<SolverType, CheckBox> entry : solverChecks.entrySet()) {
            entry.getValue().setSelected(settings.containsSolver(entry.getKey()));
        }
        chkShowResultsAfterExecution.setSelected(settings.isShowResultsAfterExecution());
        chkStoreSMTTranslationToFile.setSelected(settings.isStoreSMTTranslationToFile());
        chkStoreTacletTranslationToFile.setSelected(settings.isStoreTacletTranslationToFile());
        chkEnableOnLoad.setSelected(settings.isEnableOnLoad());
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        ProofIndependentSMTSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        // menu: MP4 — the settings API persists a single active solver name (the Swing SMT
        // toolbar selection writes it via setActiveSolverUnion → setActiveSolver,
        // MainWindow.java:744-750); a checked box stores its solver as the active solver, an
        // unchecked box cannot remove the solver from the settings' solverTypes collection
        // (no add/remove API, KNOWN-DEFERRED, see solverChecks).
        for (Map.Entry<SolverType, CheckBox> entry : solverChecks.entrySet()) {
            if (entry.getValue().isSelected()) {
                settings.setActiveSolver(entry.getKey().getName());
            }
        }
        settings.setShowResultsAfterExecution(chkShowResultsAfterExecution.isSelected());
        settings.setStoreSMTTranslationToFile(chkStoreSMTTranslationToFile.isSelected());
        settings.setStoreTacletTranslationToFile(chkStoreTacletTranslationToFile.isSelected());
        settings.setEnableOnLoad(chkEnableOnLoad.isSelected());
    }

    // menu: MP4 — no priority override, like the Swing SMTSettingsProvider (the default
    // priority 0 places SMT between "Appearance & Behaviour" (MIN_VALUE) and the javac options
    // (10000), the same relative order as the Swing SettingsManager registration).
}
