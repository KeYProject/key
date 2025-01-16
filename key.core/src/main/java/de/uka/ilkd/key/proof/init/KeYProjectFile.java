/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.DependencyRepository;
import de.uka.ilkd.key.proof.mgt.Project;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.collection.ImmutableSet;

import com.google.gson.Gson;
import com.google.gson.JsonParseException;
import org.jspecify.annotations.NonNull;

public class KeYProjectFile implements EnvInput {
    private final KeYUserProblemFile projectKeYFile;
    private final Path projectFolder;
    private final FileRepo fileRepo;
    private final ProblemLoaderControl control;
    private final Profile profile;
    private InitConfig initConfig;
    private Path dependenciesPath;
    private Dependencies dependencies;
    private final Project project;

    public KeYProjectFile(File folder, FileRepo fileRepo, ProblemLoaderControl control,
            Profile profile) {
        projectKeYFile = new KeYUserProblemFile("project.key",
            folder.toPath().resolve("project.key").toFile(), control, profile);
        this.projectFolder = folder.toPath().toAbsolutePath().normalize();
        this.fileRepo = fileRepo;
        this.control = control;
        this.profile = profile;
        dependenciesPath = projectFolder.resolve("src").resolve("main").resolve("key")
                .resolve("dependencies.json");
        project = Project.create(this);
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
        return warnings.union(readDependencies());
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

    private ImmutableSet<PositionedString> readDependencies() {
        // TODO: check license of GSON!
        Gson gson = new Gson();
        ImmutableSet<PositionedString> warnings = ImmutableSet.empty();
        try {
            String content = Files.readString(dependenciesPath);
            this.dependencies = gson.fromJson(content, Dependencies.class);

            // add entries from json file to DependencyRepository
            DependencyRepository depRepo = initConfig.getServices().getProject().getDepRepo();
            SpecificationRepository specRepo =
                initConfig.getServices().getSpecificationRepository();
            depRepo.registerContracts(specRepo);
            for (ContractInfo c : dependencies.contracts()) {
                Contract from = specRepo.getContractByName(c.name());
                for (DependencyEntry d : c.dependencies()) {
                    Contract to = specRepo.getContractByName(d.name());
                    depRepo.addDependency(from, to);
                }
            }
        } catch (JsonParseException e) {
            warnings = warnings.add(new PositionedString(e.getMessage(), dependenciesPath.toUri()));
        } catch (IOException e) {
            // TODO: Create empty dependencies file?
            throw new RuntimeException(e);
        }
        return warnings;
    }

    public void flush() {
        List<ContractInfo> cis = new ArrayList<>();
        for (var c : project.getDepRepo().getContractsWithDependencies()) {
            List<DependencyEntry> deps = new ArrayList<>();
            for (var d : project.getDepRepo().getDependencies(c)) {
                deps.add(new DependencyEntry(d.getName(), d.hashCode()));
            }
            cis.add(new ContractInfo(c.getName(), c.hashCode(), -1, ProofStatus.OPEN, deps));
        }
        var dependencies = new Dependencies(cis);
        // Write
        var gson = new Gson();
        try {
            Files.writeString(dependenciesPath, gson.toJson(dependencies), StandardCharsets.UTF_8);
        } catch (IOException e) {
            // TODO: DD: Logging
            throw new RuntimeException(e);
        }
    }

    public Path getPath() {
        return projectFolder;
    }

    private record Dependencies(List<ContractInfo> contracts) {
    }

    private record ContractInfo(String name, int hash, int srcHash, ProofStatus state,
            List<DependencyEntry> dependencies) {}

    private record DependencyEntry(String name, int hash) {}
}
