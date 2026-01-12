package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYProjectFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.PositionedString;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableSet;

import java.nio.file.Path;
import java.util.WeakHashMap;

public sealed interface Project extends ProofDisposedListener permits DummyProject {

    // design decision: restriction to have only a single project per path
    WeakHashMap<Path, Project> PROJECTS = new WeakHashMap<>();

    static HeavyweightProject createHeavyweight(Path projectFolder) {
        return (HeavyweightProject) PROJECTS.computeIfAbsent(projectFolder,
            p -> new HeavyweightProject(projectFolder));
    }

    static LightweightProject createLightweight(EnvInput input) {
        return (LightweightProject) PROJECTS.computeIfAbsent(input.getInitialFile().toPath(),
            p -> new LightweightProject(input.getInitialFile().toPath()));
    }

    static DummyProject createDummy() {
        return DummyProject.DUMMY;
    }


    Path getProofDir();

    DependencyRepository getDepRepo();

    void registerProof(ProofOblInput po, Proof proof);

    void addStoredProof(Contract contract, Path path);

    void addOutdatedProof(Path path);

    void setInitConfig(InitConfig ic);

    @Nullable
    Path findStoredProof(Contract contract);

    void flushAll();

    void flushSingleProof(Proof proof);

    void writeProofToDisk(Proof proof);

    @Override
    void proofDisposing(ProofDisposedEvent e);

    ImmutableSet<PositionedString> readDependencies();

    void flush();

    @Override
    void proofDisposed(ProofDisposedEvent e);
}
