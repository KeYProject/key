package key.isabelletranslation;

import java.util.Collection;

public interface IsabelleLauncherListener {
    void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolverInstance> finishedInstances);

    void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleProblem> problems);
}
