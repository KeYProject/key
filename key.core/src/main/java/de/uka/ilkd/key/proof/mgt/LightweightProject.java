package de.uka.ilkd.key.proof.mgt;

import com.google.gson.Gson;
import com.google.gson.JsonParseException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.MiscTools;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableSet;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

public sealed class LightweightProject extends DummyProject permits HeavyweightProject {
    protected final DependencyRepository depRepo;
    protected final Path initialPath;
    protected final Path proofDir = Paths.get("src", "main", "key", "proofs");

    /**
     * Invariant: The keys of {@code loadedProofs} are a subset of the keys of {@code storedProofs}. The former
     * holds all proofs loaded in the UI. The latter holds the paths where the proofs are saved (or
     * will be saved if the proof has been created in the current session).
     */
    protected final Map<Contract, Proof> loadedProofs = new HashMap<>();
    protected final Map<Contract, Path> storedProofs = new HashMap<>();
    // TODO: implement cleaning functionality when saving proofs ...
    protected final Set<Path> outdatedProofs = new HashSet<>();
    protected Path dependenciesPath;

    private InitConfig initConfig;

    public LightweightProject(Path initialPath) {
        this.initialPath = initialPath;
        this.depRepo = new DependencyRepository();
    }

    @Override
    public Path getProofDir() {
        return proofDir;
    }

    @Override
    public DependencyRepository getDepRepo() {
        return depRepo;
    }

    @Override
    public void registerProof(ProofOblInput po, Proof proof) {
        if (po instanceof ContractPO cpo) {
            Contract contract = cpo.getContract();
            // must be atomic contracts ...
            assert !contract.getName()
                .contains(SpecificationRepository.CONTRACT_COMBINATION_MARKER);
            loadedProofs.put(contract, proof);
        }
        // TODO: WP: warning when registering non-contract-POs?
    }

    @Override
    public void addStoredProof(Contract contract, Path path) {
        storedProofs.put(contract, path);
    }

    @Override
    public void addOutdatedProof(Path path) {
        outdatedProofs.add(path);
    }

    @Override
    public void setInitConfig(InitConfig ic) {
        initConfig = ic;
    }

    @Override
    public @Nullable Path findStoredProof(Contract contract) {
        return storedProofs.get(contract);
    }

    public void flushAll() {
    }

    public void flushSingleProof(Proof proof) {
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
    }

    public ImmutableSet<PositionedString> readDependencies() {
        // TODO: check license of GSON!
        Gson gson = new Gson();
        ImmutableSet<PositionedString> warnings = ImmutableSet.empty();
        try {
            String content = Files.readString(dependenciesPath);
            var dependencies = gson.fromJson(content, DummyProject.Dependencies.class);

            // add entries from json file to DependencyRepository
            DependencyRepository depRepo = initConfig.getServices().getProject().getDepRepo();
            SpecificationRepository specRepo =
                initConfig.getServices().getSpecificationRepository();
            depRepo.registerContracts(specRepo);
            for (DummyProject.ContractInfo c : dependencies.contracts()) {
                Contract from = specRepo.getContractByName(c.name());
                for (DummyProject.DependencyEntry d : c.dependencies()) {
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

    /**
     * Writes all the dependencies of the project into {@code dependencies.json}.
     */
    public void flush() {
        List<DummyProject.ContractInfo> cis = new ArrayList<>();
        for (Contract c : getDepRepo().getContractsWithDependencies()) {
            List<DummyProject.DependencyEntry> deps = new ArrayList<>();
            for (Contract d : getDepRepo().getDependencies(c)) {
                deps.add(new DummyProject.DependencyEntry(d.getName(), d.hashCode()));
            }
            cis.add(new DummyProject.ContractInfo(c.getName(), c.hashCode(), -1, ProofStatus.OPEN, deps));
        }
        DummyProject.Dependencies dependencies = new DummyProject.Dependencies(cis);
        // Write
        Gson gson = new Gson();
        try {
            Files.writeString(dependenciesPath, gson.toJson(dependencies), StandardCharsets.UTF_8);
        } catch (IOException e) {
            // TODO: DD: Logging
            throw new RuntimeException(e);
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
    }
}
