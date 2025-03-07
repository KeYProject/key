/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.util.Collection;

/**
 * Interface for listener classes for the {@link IsabelleLauncher}
 */
public interface IsabelleLauncherListener {
    /**
     * Called when the launcher has stopped (both successfully and due to interruptions etc.).
     *
     * @param launcher The stopped launcher
     * @param finishedInstances The instances which have finished processing in the launcher.
     */
    void launcherStopped(IsabelleLauncher launcher, Collection<IsabelleSolver> finishedInstances);

    void launcherStarted(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers);

    void launcherPreparationFinished(IsabelleLauncher launcher, Collection<IsabelleSolver> solvers);
}
