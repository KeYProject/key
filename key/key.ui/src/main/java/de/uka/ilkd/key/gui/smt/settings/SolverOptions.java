package de.uka.ilkd.key.gui.smt.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SolverType;

import javax.swing.*;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
class SolverOptions extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = 4425059748947494605L;
    private static final String infoSolverName =
            "There are two ways to make supported provers applicable for KeY:\n"
                    + "1. Specify the absolute path of the prover in the field 'Command'.\n"
                    + "2. Change the environment variable $PATH of your system, so that it "
                    + "refers to the installed prover. In that case you must specify the name of the solver in 'Command'";
    private static final String infoSolverParameters = "In this field you can specify which parameters are passed to the " +
            "solver when the solver is started. Note that the default parameters are crucial for a stable run of the" +
            "solver.";
    private static final String infoSolverCommand = "The command for the solver.\n\n" +
            "Either you specify the absolute path of your solver or just the command for starting it.\n" +
            "In the latter case you have to modify the PATH-variable of your system.\n" +
            "Please note that you also have to specify the filename extension\n" +
            "For example: z3.exe";
    private static final String infoSolverSupport = "For the KeY system only some particular versions of this solver " +
            "have been tested. It is highly recommended to use those versions, because otherwise it is not guaranteed that " +
            "the connection to this solver is stable.\n\n" +
            "If you want to check whether the installed solver is supported, please click on the button below.\n\n";
    private static final String solverSupportText[] = {"Version of solver is supported.",
            "Version of solver may not be supported.",
            "Support has not been checked, yet."};
    private static final int SOLVER_SUPPORTED = 0;


    //private JButton    checkForSupportButton;
    private static final int SOLVER_NOT_SUPPOTED = 1;
    private static final int SOLVER_SUPPORT_NOT_CHECKED = 2;
    private final SolverType solverType;
    private final JTextField solverCommand;
    private final JTextField solverParameters;
    private ProofIndependentSMTSettings settings;

    public SolverOptions(SolverType solverType) {
        this.setName(solverType.getName());
        this.solverType = solverType;
        setHeaderText("SMT Solver: "+getDescription());

        JTextField solverName = createSolverName();
        JTextField solverInstalled = createSolverInstalled();
        solverCommand = createSolverInstalled();
        solverParameters = createSolverParameters();
        JTextField solverSupported = createSolverSupported();
        JButton toDefaultButton = createButtons();
    }

    /*protected void setSmtSettings() {
        createSolverInstalled().setText(Boolean.toString(solverType.isInstalled(true)));
    }*/

    protected JButton createButtons() {
        JButton toDefaultButton = new JButton("Set parameters to default.");
        toDefaultButton.addActionListener(arg0 -> {
            createSolverParameters().setText(solverType.getDefaultSolverParameters());
            settings.setParameters(solverType, solverParameters.getText());

        });
        addRowWithHelp(null, new JLabel(), toDefaultButton);
        return toDefaultButton;
//		checkForSupportButton = new JButton("Check for support.");
//		checkForSupportButton.addActionListener(new ActionListener() {
//
//			@Override
//			public void actionPerformed(ActionEvent arg0) {
//				solverType.checkForSupport();
//				createSolverSupported().setText(getSolverSupportText());
//			}
//		});
//		checkForSupportButton.setEnabled(solverType.isInstalled(false));

//		Box box  = addRowWithHelp(null,toDefaultButton,checkForSupportButton);
//        Box box = addRowWithHelp(null, toDefaultButton);
//      box.add(Box.createHorizontalGlue());
    }

    private String createSupportedVersionText() {
        String[] versions = solverType.getSupportedVersions();
        String result = versions.length > 1 ? "The following versions are supported: " :
                "The following version is supported: ";
        for (int i = 0; i < versions.length; i++) {
            result += versions[i];
            result += i < versions.length - 1 ? ", " : "";
        }
        return result;
    }

    private String getSolverSupportText() {
        if (solverType.supportHasBeenChecked()) {
            return solverType.isSupportedVersion() ? solverSupportText[SOLVER_SUPPORTED] : solverSupportText[SOLVER_NOT_SUPPOTED];
        } else {
            return solverSupportText[SOLVER_SUPPORT_NOT_CHECKED];
        }
    }

    protected JTextField createSolverSupported() {
        JTextField txt = addTextField("Support", getSolverSupportText(),
                infoSolverSupport + createSupportedVersionText(), null);
        txt.setEditable(false);
        return txt;
    }


    protected JTextField createSolverParameters() {
        return addTextField("Parameters", solverType.getSolverParameters(), infoSolverParameters,
                e -> settings.setParameters(solverType, solverParameters.getText()));
    }

    public JTextField createSolverCommand() {
        return addTextField("Command",
                solverType.getSolverCommand(),
                infoSolverCommand, e -> settings.setCommand(solverType, solverCommand.getText()));
    }


    protected JTextField createSolverInstalled() {
        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = info + (versionString.startsWith("version") ? " (" : " (version ") + versionString + ")";
        }
        JTextField txt = addTextField("Installed", info, "", null);
        txt.setBackground(this.getBackground());
        txt.setEditable(false);
        return txt;
    }

    protected JTextField createSolverName() {
        JTextField txt = addTextField("Name", solverType.getName(), infoSolverName, null);
        txt.setBackground(this.getBackground());
        txt.setEditable(false);
        return txt;
    }

    @Override
    public String getDescription() {
        return solverType.getName();
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        settings = SettingsManager.getSmtPiSettings().clone();
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {

    }
}
