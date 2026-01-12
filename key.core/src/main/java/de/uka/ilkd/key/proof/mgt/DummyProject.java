package de.uka.ilkd.key.proof.mgt;

import com.google.gson.Gson;
import com.google.gson.JsonParseException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYProjectFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
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

public sealed class DummyProject implements Project permits LightweightProject {
    static final DummyProject DUMMY = new DummyProject();
    @Override
    public Path getProofDir() {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");
    }

    @Override
    public DependencyRepository getDepRepo() {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");
    }

    @Override
    public void registerProof(ProofOblInput po, Proof proof) {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");

    }

    @Override
    public void addStoredProof(Contract contract, Path path) {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");

    }

    @Override
    public void addOutdatedProof(Path path) {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");
    }

    @Override
    public void setInitConfig(InitConfig ic) {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");
    }

    @Override
    public @Nullable Path findStoredProof(Contract contract) {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");
    }

    @Override
    public void flushAll() {}

    @Override
    public void flushSingleProof(Proof proof) {
    }

    @Override
    public void writeProofToDisk(Proof proof) {

    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {

    }

    @Override
    public ImmutableSet<PositionedString> readDependencies() {
        throw new UnsupportedOperationException("Cannot call this method in Dummy project");
    }

    /**
     * Writes all the dependencies of the project into {@code dependencies.json}.
     */
    @Override
    public void flush() {

    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
    }

    protected record ContractInfo(String name, int hash, int srcHash, ProofStatus state,
                                List<DependencyEntry> dependencies) {
    }

    protected record Dependencies(List<ContractInfo> contracts) {
    }

    protected record DependencyEntry(String name, int hash) {
    }
}
