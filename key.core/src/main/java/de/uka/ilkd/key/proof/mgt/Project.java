/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.nio.file.Path;
import java.util.WeakHashMap;

import de.uka.ilkd.key.proof.init.KeYProjectFile;

import org.jspecify.annotations.Nullable;

public class Project {
    public static final Project DUMMY = new Project();
    public static final WeakHashMap<Path, Project> PROJECTS = new WeakHashMap<>();

    private final DependencyRepository depRepo;
    private final @Nullable KeYProjectFile projectFile;

    private Project(KeYProjectFile projectFile) {
        this.depRepo = new DependencyRepository();
        this.projectFile = projectFile;
        Runtime.getRuntime().addShutdownHook(new Thread(this::flush));
    }

    public static Project create(KeYProjectFile projectFile) {
        return PROJECTS.computeIfAbsent(projectFile.getPath(),
            k -> new Project(projectFile));
    }

    public Project() {
        // TODO: DD: What do we do here?
        this.depRepo = new DependencyRepository();
        this.projectFile = null;
    }

    public DependencyRepository getDepRepo() {
        return depRepo;
    }

    public void flush() {
        if (projectFile != null) {
            projectFile.flush();
        }
    }
}
