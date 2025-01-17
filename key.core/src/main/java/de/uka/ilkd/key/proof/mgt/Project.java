/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.KeYProjectFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

import org.jspecify.annotations.Nullable;

public class Project implements ProofDisposedListener {
    public static final Project DUMMY = new Project();
    public static final WeakHashMap<Path, Project> PROJECTS = new WeakHashMap<>();

    private final DependencyRepository depRepo;
    private final @Nullable KeYProjectFile projectFile;
    private final Path proofDir = Paths.get("src", "main", "key", "proofs");

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
        Runtime.getRuntime().addShutdownHook(new Thread(this::flushAll));
        /*
         * Runtime.getRuntime().addShutdownHook(new Thread( () -> {
         * loadedProofs.forEach((key, value) -> value.dispose());
         * }
         * ));
         */
    }

    public static Project create(KeYProjectFile projectFile) {
        return PROJECTS.computeIfAbsent(projectFile.getInitialPath(),
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

    public void registerProof(ProofOblInput po, Proof proof) {
        if (po instanceof ContractPO cpo) {
            Contract contract = cpo.getContract();
            // must be atomic contracts ...
            assert !contract.getName()
                    .contains(SpecificationRepository.CONTRACT_COMBINATION_MARKER);
            loadedProofs.put(contract, proof);
            if (projectFile != null) {
                String proofName = MiscTools.toValidFileName(contract.getName()) + ".proof";
                Path proofPath = projectFile.getInitialPath().resolve(proofDir).resolve(proofName);
                storedProofs.put(contract, proofPath);
                proof.addProofDisposedListener(this);
            }
        }
        // TODO: WP: warning when registering non-contract-POs?
    }

    public @Nullable Path findStoredProof(Contract contract) {
        return storedProofs.get(contract);
    }

    public void flushAll() {
        if (projectFile != null) {
            projectFile.flush();
            loadedProofs.entrySet().forEach(e -> writeProofToDisk(e.getValue()));
        }
    }

    public void flushSingleProof(Proof proof) {
        if (projectFile != null) {
            writeProofToDisk(proof);
        }
    }

    public void writeProofToDisk(Proof proof) {
        Contract c = loadedProofs.entrySet().stream().filter(e -> e.getValue() == proof).findFirst()
                .get().getKey();
        Path p = storedProofs.get(c);
        try {
            Files.createDirectories(p.getParent());
            ProofSaver.saveToFile(p.toFile(), proof);
        } catch (IOException e) {
            // TODO: WP: logging
            throw new RuntimeException(e);
        }
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        Proof source = e.getSource();
        Contract c = null;
        for (Map.Entry<Contract, Proof> entry : loadedProofs.entrySet()) {
            if (entry.getValue() == source) {
                c = entry.getKey();
                break;
            }
        }
        flushSingleProof(source);
        if (c != null) {
            loadedProofs.remove(c, source);
        }
        if (projectFile != null) {
            projectFile.flush();
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
    }
}
