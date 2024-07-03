/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.gui.smt.settings;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.st.SolverType;

import static de.uka.ilkd.key.gui.smt.settings.SMTSettingsProvider.BUNDLE;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
class SolverOptions extends SettingsPanel implements SettingsProvider {
    private static final String INFO_SOLVER_NAME = "infoSolverName";
    private static final String INFO_SOLVER_PARAMETERS = "infoSolverParameters";
    private static final String INFO_SOLVER_COMMAND = "infoSolverCommand";
    private static final String INFO_SOLVER_SUPPORT = "infoSolverSupport";
    private static final String[] solverSupportText = {
        BUNDLE.getString("SOLVER_SUPPORTED"),
        BUNDLE.getString("SOLVER_MAY_SUPPORTED"),
        BUNDLE.getString("SOLVER_UNSUPPORTED") };
    private static final String INFO_SOLVER_TIMEOUT = "SOLVER_TIMEOUT";

    private static final int SOLVER_SUPPORTED = 0;

    private static final int SOLVER_NOT_SUPPOTED = 1;
    private static final int SOLVER_SUPPORT_NOT_CHECKED = 2;
    private final SolverType solverType;
    private final JTextField solverCommand;
    private final JTextField solverParameters;
    private final JTextField solverSupported;
    private final JTextField solverName;
    private final JTextField solverInstalled;
    private final JSpinner solverTimeout;

    public SolverOptions(SolverType solverType) {
        this.setName(solverType.getName());
        this.solverType = solverType;
        setHeaderText("SMT Solver: " + getDescription());

        solverName = createSolverName();
        solverInstalled = createSolverInstalled();
        solverCommand = createSolverCommand();
        solverTimeout = createSolverTimeout();
        solverParameters = createSolverParameters();
        solverSupported = createSolverSupported();
        createDefaultButton();
        createCheckSupportButton();
    }


    protected JButton createDefaultButton() {
        JButton toDefaultButton = new JButton("Set parameters to default");
        toDefaultButton.addActionListener(
            arg0 -> solverParameters.setText(solverType.getDefaultSolverParameters()));
        addRowWithHelp(null, new JLabel(), toDefaultButton);
        return toDefaultButton;
    }

    private String createSupportedVersionText() {
        String[] versions = solverType.getSupportedVersions();
        StringBuilder result =
            new StringBuilder(versions.length > 1 ? "The following versions are supported: "
                    : "The following version is supported: ");
        for (int i = 0; i < versions.length; i++) {
            result.append(versions[i]);
            result.append(i < versions.length - 1 ? ", " : "");
        }
        return result.toString();
    }

    private String getSolverSupportText() {
        if (solverType.supportHasBeenChecked()) {
            return solverType.isSupportedVersion()
                    ? solverSupportText[SOLVER_SUPPORTED]
                    : solverSupportText[SOLVER_NOT_SUPPOTED];
        } else {
            return solverSupportText[SOLVER_SUPPORT_NOT_CHECKED];
        }
    }

    protected JTextField createSolverSupported() {

        JTextField txt = addTextField("Support", getSolverSupportText(),
            BUNDLE.getString(INFO_SOLVER_SUPPORT) + createSupportedVersionText(), null);
        txt.setEditable(false);
        return txt;
    }

    private JSpinner createSolverTimeout() {
        var model = new SpinnerNumberModel(Long.valueOf(0L), Long.valueOf(-1L),
            Long.valueOf(Long.MAX_VALUE),
            Long.valueOf(1L));
        var jsp = createNumberTextField(model, null);
        addTitledComponent("Timeout", jsp, BUNDLE.getString(INFO_SOLVER_TIMEOUT));
        return jsp;
    }


    protected JButton createCheckSupportButton() {
        JButton checkForSupportButton = new JButton("Check for support");
        checkForSupportButton.setEnabled(solverType.isInstalled(false));
        checkForSupportButton.addActionListener(arg0 -> {
            solverType.checkForSupport();
            solverSupported.setText(getSolverSupportText());
        });
        addRowWithHelp(null, new JLabel(), checkForSupportButton);
        return checkForSupportButton;
    }

    protected JTextField createSolverParameters() {
        return addTextField("Parameters", solverType.getSolverParameters(),
            BUNDLE.getString(INFO_SOLVER_PARAMETERS),
            e -> {
            });
    }

    public JTextField createSolverCommand() {
        return addTextField("Command",
            solverType.getSolverCommand(),
            BUNDLE.getString(INFO_SOLVER_COMMAND), e -> {
            });
    }


    protected JTextField createSolverInstalled() {
        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString;
            try {
                versionString = solverType.getRawVersion();
                info = info + (versionString.startsWith("version") ? " (" : " (version ")
                    + versionString + ")";
            } catch (RuntimeException re) {
                // this case occurs for instance, if there user can see e.g. z3 but has not the
                // permission
                // to execute the solver
                info =
                    "(version: unknown) solver is installed, but trying to access it resulted in an error "
                        +
                        (re.getCause() != null ? re.getCause().getLocalizedMessage()
                                : re.getLocalizedMessage());
            }
        }
        JTextField txt = addTextField("Installed", info, "", null);
        txt.setEditable(false);
        return txt;
    }

    protected JTextField createSolverName() {
        JTextField txt =
            addTextField("Name", solverType.getName(), BUNDLE.getString(INFO_SOLVER_NAME), null);
        txt.setEditable(false);
        return txt;
    }

    @Override
    public String getDescription() {
        return solverType.getName();
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        setSmtSettings(SettingsManager.getSmtPiSettings().clone());
        return this;
    }

    private void setSmtSettings(ProofIndependentSMTSettings clone) {
        final var solverData = clone.getSolverData(solverType);
        if (solverData != null) {
            solverCommand.setText(solverData.getSolverCommand());
            solverParameters.setText(solverData.getSolverParameters());
            solverTimeout.setValue((Long) solverData.getTimeout() / 1000L);
            solverName.setText(solverType.getName());
        } else {
            throw new IllegalStateException("Could not find solver data for type: " + solverType);
        }

        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = info + (versionString.startsWith("version") ? " (" : " (version ")
                + versionString + ")";
        }
        solverInstalled.setText(info);
    }

    @Override
    public void applySettings(MainWindow window) {
        var settings = SettingsManager.getSmtPiSettings();
        final var solverData = settings.getSolverData(solverType);
        if (solverData != null) {
            String command = solverCommand.getText();
            String params = solverParameters.getText();
            long timeout = ((Long) solverTimeout.getValue()) * 1000L;

            solverData.setTimeout(timeout);
            solverData.setSolverCommand(command);
            solverData.setSolverParameters(params);

            solverType.setSolverCommand(command);
            solverType.setSolverParameters(params);
            // This is not necessary as it just calls solverData.setSolver... again
            // SettingsManager.getSmtPiSettings().setCommand(solverType, command);
            // SettingsManager.getSmtPiSettings().setParameters(solverType, params);
            window.updateSMTSelectMenu();

            setSmtSettings(SettingsManager.getSmtPiSettings().clone()); // refresh gui
        } else {
            throw new IllegalStateException("Could not find solver data for type: " + solverType);
        }
    }
}
