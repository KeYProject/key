package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.smt.VersionChecker;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
abstract class AbstractSolverType implements SolverType {
    private boolean installWasChecked = false;
    private boolean isInstalled = false;
    private String solverParameters = getDefaultSolverParameters();
    private String solverCommand = getDefaultSolverCommand();
    private String solverVersion = "";
    private boolean isSupportedVersion = false;
    private boolean supportHasBeenChecked = false;


    public static boolean isInstalled(String cmd) {


        if (checkEnvVariable(cmd)) {
            return true;
        } else {

            File file = new File(cmd);

            return file.exists() && !file.isDirectory();

        }
    }


    /**
     * check, if this solver is installed and can be used.
     *
     * @param recheck if false, the solver is not checked again, if a cached
     *                value for this exists.
     * @return true, if it is installed.
     */
    @Override
    public boolean isInstalled(boolean recheck) {
        if (recheck || !installWasChecked) {

            String cmd = getSolverCommand();

            isInstalled = isInstalled(cmd);
            if (isInstalled) {
                installWasChecked = true;
            }

        }
        return isInstalled;
    }

    private static boolean checkEnvVariable(String cmd) {
        String path = System.getenv("PATH");

        String[] res = path.split(File.pathSeparator);
        for (String s : res) {
            File file = new File(s + File.separator + cmd);
            if (file.exists()) {
                return true;
            }
        }

        return false;

    }

    @Override
    public boolean checkForSupport() {
        if (!isInstalled) {
            return false;
        }
        supportHasBeenChecked = true;
        solverVersion = getRawVersion();
        if (solverVersion == null) {
            solverVersion = "";
            isSupportedVersion = false;
            return false;
        }
        for (String supportedVersion : getSupportedVersions()) {
            if (solverVersion.indexOf(supportedVersion) > -1) {
                isSupportedVersion = true;
                return true;
            }
        }
        isSupportedVersion = false;
        return false;
    }

    @Override
    public boolean supportHasBeenChecked() {
        return supportHasBeenChecked;
    }

    @Override
    public boolean isSupportedVersion() {
        return isSupportedVersion;
    }

    @Override
    public String getSolverParameters() {
        if (solverParameters == null) {
            return getDefaultSolverParameters();
        }
        return solverParameters;
    }

    @Override
    public void setSolverParameters(String s) {

        solverParameters = s;
    }

    @Override
    public void setSolverCommand(String s) {
        supportHasBeenChecked = false;
        solverCommand = s;
    }

    @Override
    public final String getSolverCommand() {
        if (solverCommand == null || solverCommand.isEmpty()) {
            return getDefaultSolverCommand();
        }
        return solverCommand;
    }

    @Override
    public String getVersion() {
        return solverVersion;
    }

    @Override
    public String getRawVersion() {
        if (isInstalled(true)) {
            return VersionChecker.INSTANCE.getVersionFor(getSolverCommand(), getVersionParameter());
        } else {
            return null;
        }
    }

    @Override
    public String toString() {
        return getName();
    }

    @Override
    public String modifyProblem(String problem) {
        return problem;
    }

}
