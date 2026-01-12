/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.io.IOException;
import java.nio.file.FileVisitOption;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.HeavyweightProject;
import de.uka.ilkd.key.proof.mgt.Project;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.PositionedString;

import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

public class KeYProjectFile implements EnvInput {
    private final KeYUserProblemFile projectKeYFile;
    private final Path projectFolder;
    private final FileRepo fileRepo;
    private final Profile profile;
    private final ProblemLoaderControl control;
    private InitConfig initConfig;
    private final HeavyweightProject project;

    public KeYProjectFile(File folder, FileRepo fileRepo, ProblemLoaderControl control,
            Profile profile) {
        projectKeYFile = new KeYUserProblemFile("project.key",
            folder.toPath().resolve("project.key").toFile(), control, profile);
        this.projectFolder = folder.toPath().toAbsolutePath().normalize();
        this.fileRepo = fileRepo;
        this.control = control;
        this.profile = profile;
        project = Project.createHeavyweight(projectFolder);
    }

    @Override
    public String name() {
        return projectFolder.getFileName().toString();
    }

    @Override
    public int getNumberOfChars() {
        return projectKeYFile.getNumberOfChars();
    }

    @Override
    public void setInitConfig(InitConfig initConfig) {
        this.initConfig = initConfig;
        projectKeYFile.setInitConfig(initConfig);
    }

    @Override
    public Includes readIncludes() throws ProofInputException {
        return projectKeYFile.readIncludes();
    }

    @Override
    public String readJavaPath() throws ProofInputException {
        return projectKeYFile.readJavaPath();
    }

    @Override
    public @NonNull List<File> readClassPath() throws ProofInputException {
        return projectKeYFile.readClassPath();
    }

    @Override
    public File readBootClassPath() {
        return projectKeYFile.readBootClassPath();
    }

    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        var warnings = projectKeYFile.read();
        warnings = warnings.union(project.readDependencies());
        readStoredProofs();
        return warnings;
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    @Override
    public Project getProject() {
        return project;
    }

    @Override
    public File getInitialFile() {
        return projectFolder.toFile();
    }

    public Path getInitialPath() {
        return projectFolder;
    }

    private void readStoredProofs() {
        Map<String, Contract> filename2Contract = new HashMap<>();
        initConfig.getServices().getSpecificationRepository().getAllContracts().stream().forEach(c -> filename2Contract.put(MiscTools.toValidFileName(c.getName()) + ".proof", c));
        try {
            Files.walk(projectFolder.resolve(project.getProofDir()), 1, FileVisitOption.FOLLOW_LINKS).filter(p -> p.toString().endsWith(".proof")).forEach(p -> {
                Contract c = filename2Contract.get(p.getFileName().toString());
                if (c != null) {
                    project.addStoredProof(c, p);
                } else {
                    // this proof is definitely outdated, the contract it refers to does not exist anymore
                    project.addOutdatedProof(p);
                }
            });
        } catch (IOException e) {
            // TODO: DD: Logging
            throw new RuntimeException(e);
        }
    }
}
