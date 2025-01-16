/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYProjectFile;
import de.uka.ilkd.key.speclang.Contract;

import org.jspecify.annotations.Nullable;

public class Project {
    public static final Project DUMMY = new Project();
    public static final WeakHashMap<Path, Project> PROJECTS = new WeakHashMap<>();

    private final DependencyRepository depRepo;
    private final @Nullable KeYProjectFile projectFile;

    /**
     * The keys of {@code loadedProofs} are a subset of the keys of {@code storedProofs}. The former
     * holds all proofs loaded in the UI. The latter holds the paths where the proofs are saved (or
     * will be saved if the proof has been created in the current session).
     */
    private final Map<Contract, Proof> loadedProofs = new HashMap<>();
    private final Map<Contract, Path> storedProofs = new HashMap<>();

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

    public void registerProof(Contract contract, Proof proof) {
        assert !loadedProofs.containsKey(contract);
        loadedProofs.put(contract, proof);
    }

    public @Nullable Proof findOrReplayProof(Contract contract) {
        if (loadedProofs.containsKey(contract))
            return loadedProofs.get(contract);
        if (storedProofs.containsKey(contract)) {
            // Replay proof
            Path path = storedProofs.get(contract);

        }
        return null;
    }

    public void flush() {
        if (projectFile != null) {
            projectFile.flush();
        }
    }
}
