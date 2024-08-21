package key.isabelletranslation;

import key.isabelletranslation.gui.IsabelleProgressDialog;
import key.isabelletranslation.gui.IsabelleProgressModel;

import javax.swing.*;
import java.util.Collection;

public interface IsabelleLauncherListener {
    void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolverInstance> finishedInstances);

    void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleProblem> problems);
}
