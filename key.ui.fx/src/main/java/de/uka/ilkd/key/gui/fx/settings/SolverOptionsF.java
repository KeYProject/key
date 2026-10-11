/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

/**
 * Per-solver options panel of the settings dialog, counter-part of
 * {@code de.uka.ilkd.key.gui.smt.settings.SolverOptions} of the Swing module {@code key.ui}
 * (registered there as a child provider of {@code SMTSettingsProvider},
 * SMTSettingsProvider.java:155-158).
 * <p>
 * Shows the immutable facts of one {@link SolverType} (name, info, installed version, support
 * state) and the three persisted values (command, per-solver timeout, parameters) that live on
 * the {@link SolverType} itself. All values are re-read from
 * {@link ProofIndependentSettings#DEFAULT_INSTANCE} in {@link #getPanel(MainWindowF)} (the Swing
 * original re-reads a clone there, SolverOptions.java:180-183) and written back through
 * {@link SolverType#setSolverCommand}, {@link SolverType#setSolverParameters} and
 * {@link SolverType#setSolverTimeout} in {@link #apply(MainWindowF)}
 * (SolverOptions.java:205-224).
 * <p>
 * menu: KNOWN-DEFERRED — the Swing {@code applySettings} additionally calls
 * {@code MainWindow.updateSMTSelectMenu()} (SolverOptions.java:218) to rebuild the SMT solver
 * combo box; the FX main window has no SMT select menu yet (MainWindowF has no
 * {@code updateSMTSelectMenu} counterpart), so this refresh is not applicable here.
 */
public class SolverOptionsF extends SettingsPanelF implements SettingsProviderF {

    /**
     * Help texts and support verdicts, copied from the Swing {@code SMTSettingsProvider}
     * (SMTSettingsProvider.java:62-107) so that both UIs show identical wording.
     */
    public static final String INFO_SOLVER_NAME =
        """
                There are two ways to make supported provers applicable for KeY:
                  1. Specify the absolute path of the prover in the field 'Command'.
                  2. Change the environment variable $PATH of your system, so that it
                refers to the installed prover. In that case you must specify the name of the solver in 'Command'""";
    public static final String INFO_SOLVER_COMMAND = """
            The command for the solver.

            Either you specify the absolute path of your solver or just the command for starting it.
            In the latter case you have to modify the PATH-variable of your system.
            Please note that you also have to specify the filename extension.
            For example: z3.exe""";
    public static final String INFO_SOLVER_PARAMETERS =
        """
                In this field you can specify which parameters are passed to the \
                solver when the solver is started. Note that the default parameters are crucial for a stable run of the\
                solver.""";
    public static final String INFO_SOLVER_SUPPORT =
        """
                For the KeY system only some particular versions of this solver
                have been tested. It is highly recommended to use those versions, because otherwise it is not guaranteed that
                the connection to this solver is stable.
                If you want to check whether the installed solver is supported, please click on the button below.""";
    public static final String SOLVER_SUPPORTED = "Version of solver is supported.";
    public static final String SOLVER_MAY_SUPPORTED = "Version of solver may not be supported.";
    public static final String SOLVER_UNSUPPORTED = "Support has not been checked, yet.";
    public static final String INFO_SOLVER_TIMEOUT =
        "Overrides timeout for this solver. Values in seconds. If value <= 0, global timeout is used.";
    public static final String INFO_SOLVER_INFO = "Information about this solver.";

    private final transient SolverType solverType;

    private TextField txtName;
    private TextField txtInstalled;
    private TextField txtCommand;
    private TextField txtParameters;
    private TextField txtSupported;
    private Spinner<Double> spinTimeout;

    /** Creates the panel for one solver type and builds the form once (the panel is reused). */
    public SolverOptionsF(SolverType solverType) {
        this.solverType = solverType;
        setHeaderText("SMT Solver: " + getDescription());

        txtName = createSolverName();
        createSolverInformation();
        txtInstalled = createSolverInstalled();
        txtCommand = createSolverCommand();
        spinTimeout = createSolverTimeout();
        txtParameters = createSolverParameters();
        txtSupported = createSolverSupported();
        createDefaultButton();
        createCheckSupportButton();

        refreshFromSettings();
    }

    @Override
    public String getDescription() {
        return solverType.getName();
    }

    @Override
    public Node getPanel(MainWindowF window) {
        // like the Swing original, re-read the current settings on every getPanel
        // (SolverOptions.getPanel → setSmtSettings, SolverOptions.java:180-202)
        refreshFromSettings();
        return this;
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        ProofIndependentSMTSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        if (!settings.containsSolver(solverType)) {
            throw new IllegalStateException("Could not find solver data for type: " + solverType);
        }
        String command = txtCommand.getText();
        String params = txtParameters.getText();
        long timeout = (long) (spinTimeout.getValue() * 1000.0);

        solverType.setSolverCommand(command);
        solverType.setSolverParameters(params);
        solverType.setSolverTimeout(timeout);
        // menu: KNOWN-DEFERRED — the Swing original calls window.updateSMTSelectMenu() here
        // (SolverOptions.java:218); the FX main window has no SMT select menu counterpart yet.

        refreshFromSettings(); // refresh gui
    }

    /**
     * Re-reads the current settings into the input components (Swing {@code setSmtSettings},
     * SolverOptions.java:185-202).
     */
    private void refreshFromSettings() {
        ProofIndependentSMTSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        if (!settings.containsSolver(solverType)) {
            throw new IllegalStateException("Could not find solver data for type: " + solverType);
        }
        txtCommand.setText(settings.getCommand(solverType));
        txtParameters.setText(settings.getParameters(solverType));
        spinTimeout.getValueFactory()
                .setValue(((double) settings.getSolverTimeout(solverType)) / 1000);
        txtName.setText(solverType.getName());

        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            try {
                info = versionInfo(info, solverType.getRawVersion());
            } catch (RuntimeException re) {
                // this case occurs for instance if the user can see e.g. z3 but doesn't have
                // the permission to execute the solver
                info = "(version: unknown) solver is installed, but trying to access it resulted "
                    + "in an error " + (re.getCause() != null
                            ? re.getCause().getLocalizedMessage()
                            : re.getLocalizedMessage());
            }
        }
        txtInstalled.setText(info);
    }

    private TextField createSolverName() {
        TextField txt = addTextField("Name", solverType.getName(), INFO_SOLVER_NAME,
            emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    private void createSolverInformation() {
        String info = solverType.getInfo();
        if (info != null && !info.isEmpty()) {
            TextArea area = addTextArea("Info", info, INFO_SOLVER_INFO, null, 3);
            area.setEditable(false);
        }
    }

    private TextField createSolverInstalled() {
        // initial content is refreshed in refreshFromSettings; the field is read-only
        TextField txt = addTextField("Installed", "", "", emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    private TextField createSolverCommand() {
        return addTextField("Command", solverType.getSolverCommand(), INFO_SOLVER_COMMAND,
            emptyValidator());
    }

    private Spinner<Double> createSolverTimeout() {
        // seconds with fractions, stored as milliseconds on the solver type
        // (Swing model: SpinnerNumberModel(0.0, -1.0, Long.MAX_VALUE, 1), SolverOptions.java:108)
        return addDoubleNumberField("Timeout", -1.0, (double) Long.MAX_VALUE, 1.0, 0.0,
            INFO_SOLVER_TIMEOUT, emptyValidator());
    }

    private TextField createSolverParameters() {
        return addTextField("Parameters", solverType.getSolverParameters(),
            INFO_SOLVER_PARAMETERS, emptyValidator());
    }

    private TextField createSolverSupported() {
        TextField txt = addTextField("Support", getSolverSupportText(),
            INFO_SOLVER_SUPPORT + " " + createSupportedVersionText(), emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    private String createSupportedVersionText() {
        return "The following minimal version is supported: "
            + solverType.getMinimumSupportedVersion();
    }

    private String getSolverSupportText() {
        if (solverType.supportHasBeenChecked()) {
            return solverType.isSupportedVersion() ? SOLVER_SUPPORTED : SOLVER_MAY_SUPPORTED;
        }
        return SOLVER_UNSUPPORTED;
    }

    private void createDefaultButton() {
        Button toDefaultButton = new Button("Set parameters to default");
        toDefaultButton.setOnAction(
            e -> txtParameters.setText(solverType.getDefaultSolverParameters()));
        addRowWithHelp(null, new javafx.scene.control.Label(), toDefaultButton);
    }

    private void createCheckSupportButton() {
        Button checkForSupportButton = new Button("Check for support");
        checkForSupportButton.setDisable(!solverType.isInstalled(false));
        checkForSupportButton.setOnAction(e -> {
            solverType.checkForSupport();
            txtSupported.setText(getSolverSupportText());
        });
        addRowWithHelp(null, new javafx.scene.control.Label(), checkForSupportButton);
    }

    private static String versionInfo(String info, String versionString) {
        return info + " (" + versionString + ")";
    }
}
