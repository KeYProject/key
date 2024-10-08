package org.key_project.isabelletranslation.automation;

import java.util.Collection;

public interface IsabelleLauncherListener {
    void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolver> finishedInstances);

    void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers);

    void launcherPreparationFinished(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers);
}
