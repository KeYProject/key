/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofServices;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.lookup.Lookup;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This is a collection of common services to the KeY prover. Services include information on the
 * underlying Java model and a converter to transform Java program elements to logic (where
 * possible) and back.
 */
public class Services implements TermServices, LogicServices, ProofServices {
    private static final Logger LOGGER = LoggerFactory.getLogger(Services.class);
    /**
     * the proof
     */
    private Proof proof;

    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private NamespaceSet namespaces = new NamespaceSet();

    /**
     * used to determine whether an expression is a compile-time constant and if so the type and
     * result of the expression
     */
    private final ConstantExpressionEvaluator cee;

    /**
     * used to convert types, expressions and so on to logic elements (in special into to terms or
     * formulas)
     */
    private TypeConverter typeconverter;

    /**
     * the information object on the Java model
     */
    @Nullable
    private JavaInfo javaInfo;

    /**
     * variable namer for inner renaming
     */
    private final VariableNamer innerVarNamer = new InnerVariableNamer(this);

    /**
     * map of names to counters
     */
    private final HashMap<String, Counter> counters;

    /**
     * specification repository
     */
    private SpecificationRepository specRepos;

    /*
     * the Java model (with all paths)
     */
    private JavaModel javaModel;

    /**
     * Records the fresh-name proposals made while a rule is applied, so they can be stored on the
     * node for reproducible reload. It is <em>per thread</em>: the proposals are recorded during
     * the rule's compute phase, which -- under the multi-core prover -- runs concurrently on the
     * workers, so each proving thread (the single single-core thread, or each worker) gets its own
     * recorder. This makes the recorder prover-agnostic and free of races on a shared field,
     * without {@link Services} having to know which prover is running. It is an <em>instance</em>
     * {@link ThreadLocal} (not static), so a nested side proof, which runs on its own
     * {@link Services}, keeps its own recorder. Lazily created; reset by
     * {@link #saveNameRecorder(Node)} after each rule application.
     */
    private ThreadLocal<NameRecorder> nameRecorder =
        ThreadLocal.withInitial(NameRecorder::new);

    private ITermProgramVariableCollectorFactory factory =
        TermProgramVariableCollector::new;

    private OriginTermLabelFactory originFactory;

    private final Profile profile;

    private final ServiceCaches caches;

    private final TermBuilder termBuilder;

    private final TermBuilder termBuilderWithoutCache;

    @Nullable
    private JavaService javaService;

    /**
     * creates a new Services object with a new TypeConverter and a new JavaInfo object with no
     * information stored at none of these.
     */
    public Services(Profile profile) {
        this(profile, null, new LinkedHashMap<>(), new ServiceCaches());
    }

    private Services(Profile profile, @Nullable JavaService javaService,
            HashMap<String, Counter> counters,
            ServiceCaches caches) {
        assert profile != null;
        assert counters != null;
        assert caches != null;

        this.profile = profile;
        this.counters = counters;
        this.caches = caches;
        this.termBuilder = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
        this.termBuilderWithoutCache = new TermBuilder(new TermFactory(), this);
        this.specRepos = profile.createSpecificationRepository(this);
        this.cee = new ConstantExpressionEvaluator();
        typeconverter = new TypeConverter(this);
        if (javaService == null) {
            this.javaService = null;
            this.javaInfo = null;
        } else {
            this.javaService = javaService.copy(this);
            this.javaInfo = new JavaInfo(new KeYProgModelInfo(this.javaService), this);
        }
    }

    private Services(Services s) {
        this.profile = s.profile;
        this.proof = s.proof;
        this.namespaces = s.namespaces;
        this.cee = s.cee;
        this.typeconverter = s.typeconverter;
        this.javaInfo = s.javaInfo;
        this.counters = s.counters;
        this.specRepos = s.specRepos;
        this.javaModel = s.javaModel;
        // Share the (per-thread) recorder with the source: an overlay (see getOverlay) is the
        // services the rule executor works through, and fresh-name proposals set on the base
        // services -- e.g. by the proof replayer before re-applying a rule -- must be visible and
        // consumable through it. This mirrors the pre-ThreadLocal field aliasing; per-thread
        // isolation between proving threads is preserved because it is the ThreadLocal that is
        // shared, not a recorder instance.
        this.nameRecorder = s.nameRecorder;
        this.factory = s.factory;
        this.caches = s.caches;
        this.javaService = s.javaService;
        this.termBuilder = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
        this.termBuilderWithoutCache = new TermBuilder(new TermFactory(), this);
        this.originFactory = s.originFactory;
    }

    public Services getOverlay(NamespaceSet namespaces) {
        Services result = new Services(this);
        result.setNamespaces(namespaces);
        return result;
    }

    /**
     * Returns the TypeConverter associated with this Services object.
     */
    public TypeConverter getTypeConverter() {
        return typeconverter;
    }


    private void setTypeConverter(TypeConverter tc) {
        typeconverter = tc;
    }

    public JavaDLTheory getJavaDLTheory() {
        return typeconverter.getJavaDLTheory();
    }

    /**
     * Returns the ConstantExpressionEvaluator associated with this Services object.
     */
    public ConstantExpressionEvaluator getConstantExpressionEvaluator() {
        return cee;
    }


    /**
     * Returns the JavaInfo associated with this Services object.
     */
    @NonNull
    public JavaInfo getJavaInfo() {
        return Objects.requireNonNull(javaInfo);
    }


    /**
     * The name recorder for the calling thread (see the {@link #nameRecorder} field).
     *
     * @return the calling thread's name recorder
     */
    public NameRecorder getNameRecorder() {
        return nameRecorder.get();
    }

    /**
     * Stores the calling thread's recorded name proposals on the given node and starts a fresh
     * recorder for that thread's next rule application.
     *
     * @param n the node to store the recorded proposals on
     */
    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder.get());
        nameRecorder.set(new NameRecorder());
    }


    public void addNameProposal(Name proposal) {
        getNameRecorder().addProposal(proposal);
    }


    public SpecificationRepository getSpecificationRepository() {
        return specRepos;
    }


    /**
     * Returns the VariableNamer associated with this Services object.
     */
    public VariableNamer getVariableNamer() {
        return innerVarNamer;
    }

    /**
     * creates a new services object containing a copy of the java info of this object and a new
     * TypeConverter (shallow copy) The copy does not belong to a {@link Proof} object and can hence
     * be used for a new proof.
     *
     * @param shareCaches {@code true} The created {@link Services} will use the same
     *        {@link ServiceCaches} like this instance; {@code false} the created {@link Services}
     *        will use a new empty {@link ServiceCaches} instance.
     * @return the copy
     */
    public Services copy(boolean shareCaches) {
        return copy(getProfile(), shareCaches);
    }

    /**
     * Creates a copy of this {@link Services} in which the {@link Profile} is replaced. The copy
     * does not belong to a {@link Proof} object and can hence be used for a new proof.
     *
     * @param profile The new {@link Profile} to use in the copy of this {@link Services}.
     * @param shareCaches {@code true} The created {@link Services} will use the same
     *        {@link ServiceCaches} like this instance; {@code false} the created {@link Services}
     *        will use a new empty {@link ServiceCaches} instance.
     * @return The created copy.
     */
    public Services copy(Profile profile, boolean shareCaches) {
        ServiceCaches newCaches = shareCaches ? caches : new ServiceCaches();
        Services s = new Services(profile, javaService, copyCounters(), newCaches);
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        // Detach this instance's recorder from earlier overlays/aliases, keeping the calling
        // thread's current contents (mirrors the pre-ThreadLocal `nameRecorder =
        // nameRecorder.copy()`): the copy is the basis of a NEW proof, whose recordings must not
        // leak into recorders already stored on this services' nodes.
        NameRecorder detached = nameRecorder.get().copy();
        nameRecorder = ThreadLocal.withInitial(NameRecorder::new);
        nameRecorder.set(detached);
        s.setJavaModel(getJavaModel());
        s.originFactory = originFactory;
        return s;
    }

    /**
     * Creates a deep copy of {@link #counters} which means that a new list is created with a copy
     * of each contained {@link Counter}.
     *
     * @return The created deep copy with new {@link Counter} instances.
     */
    private HashMap<String, Counter> copyCounters() {
        HashMap<String, Counter> result = new LinkedHashMap<>();
        for (Entry<String, Counter> entry : counters.entrySet()) {
            result.put(entry.getKey(), entry.getValue().copy());
        }
        return result;
    }

    /**
     * creates a new service object with the same ldt information as the actual one
     */
    public Services copyPreservesLDTInformation() {
        Services s =
            new Services(getProfile(), javaService, new LinkedHashMap<>(), new ServiceCaches());
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        // The copy starts from this thread's current recordings (mirrors the pre-ThreadLocal
        // `s.nameRecorder = nameRecorder.copy()`).
        s.nameRecorder.set(nameRecorder.get().copy());
        s.setJavaModel(getJavaModel());
        s.originFactory = originFactory;
        return s;
    }


    /**
     * Marks this services as proof specific Please make sure that the {@link Services} does not
     * yet belong to an existing proof or that it is owned by a proof environment. In both cases
     * copy the {@link InitConfig} via {@link InitConfig#deepCopy()} or one of the other copy
     * methods first.
     *
     * @param proof the Proof to which this {@link Services} instance belongs
     */
    public void setProof(Proof proof) {
        if (this.proof != null) {
            throw new IllegalStateException(
                "Services are already owned by another proof:" + this.proof.name());
        }
        this.proof = proof;
    }


    /**
     * Returns the named proof-global counter, creating it if necessary.
     *
     * <p>
     * Synchronized so that concurrent workers cannot lose a counter through
     * a racing check-then-put on the shared counters map. The per-counter increment is atomic (see
     * {@link Counter}); this only guards lookup/creation.
     *
     * @param name the counter's name
     * @return the (possibly freshly created) counter
     * @deprecated Do not introduce new proof-global counters; prefer removing the remaining ones. A
     *             value drawn from such a counter is a function of how many times it has been
     *             advanced -- i.e. of the whole proof's history, and under the parallel prover of
     *             the worker schedule -- so any name or id derived from it that becomes part of the
     *             proof is <em>not</em> reproducible across reload, prune-and-redo or
     *             multi-threaded
     *             runs (#3851). Derive names/ids from the goal-local proof state instead: the
     *             smallest free index against the current namespace (see
     *             {@link de.uka.ilkd.key.proof.VariableNameProposer},
     *             {@link de.uka.ilkd.key.logic.VariableNamer}), a content-order number (see
     *             {@link de.uka.ilkd.key.speclang.ContentOrderNumbering}), or a dedicated field on
     *             the owning object (as the node serial number is now an
     *             {@link java.util.concurrent.atomic.AtomicInteger} on
     *             {@link de.uka.ilkd.key.proof.Proof#getNextNodeSerialNr()}). The only remaining
     *             callers are the symbolic-execution term-label counters, which are expected to be
     *             removed together with the {@code key.core.symbolic_execution} package.
     */
    @Deprecated
    public synchronized Counter getCounter(String name) {
        Counter c = counters.get(name);
        if (c != null) {
            return c;
        }
        c = new Counter(name);
        counters.put(name, c);
        return c;
    }

    /**
     * returns the namespaces for functions, predicates etc.
     *
     * @return the proof specific namespaces
     */
    @Override
    public NamespaceSet getNamespaces() {
        return namespaces;
    }

    /**
     * sets the namespaces of known predicates, functions, variables
     *
     * @param namespaces the NamespaceSet with the proof specific namespaces
     */
    public void setNamespaces(NamespaceSet namespaces) {
        this.namespaces = namespaces;
    }

    /**
     * Returns the proof to which this object belongs, or null if it does not belong to any proof.
     */
    public Proof getProof() {
        return proof;
    }

    public interface ITermProgramVariableCollectorFactory {
        TermProgramVariableCollector create(Services services);
    }

    /**
     * Returns the sued {@link Profile}.
     *
     * @return The used {@link Profile}.
     */
    public Profile getProfile() {
        return profile;
    }

    /**
     * returns the {@link JavaModel} with all path information
     *
     * @return the {@link JavaModel} on which this services is based on
     */
    public JavaModel getJavaModel() {
        return javaModel;
    }


    public void setJavaModel(JavaModel javaModel) {
        assert this.javaModel == null;
        this.javaModel = javaModel;
    }

    /**
     * Returns the used {@link ServiceCaches}.
     *
     * @return The used {@link ServiceCaches}.
     */
    public ServiceCaches getCaches() {
        return caches;
    }

    /**
     * Returns either the cache backed or raw {@link TermBuilder} used to create {@link JTerm}s.
     * Usually the cache backed version is the intended one. The non-cached version is for use cases
     * where a lot of intermediate terms are created of which most exist only for a very short time.
     * To avoid polluting the cache it is then recommended to use the non-cache version
     *
     * @return The {@link TermBuilder} used to create {@link JTerm}s.
     */
    @Override
    public TermBuilder getTermBuilder(boolean withCache) {
        return withCache ? termBuilder : termBuilderWithoutCache;
    }

    /**
     * Returns the {@link TermBuilder} used to create {@link JTerm}s. Same as
     * <code>getTermBuilder(true)</code>>.
     *
     * @return The {@link TermBuilder} used to create {@link JTerm}s.
     */
    @Override
    public TermBuilder getTermBuilder() {
        return termBuilder;
    }

    /**
     * Returns the {@link TermFactory} used to create {@link JTerm}s.
     *
     * @return The {@link TermFactory} used to create {@link JTerm}s.
     */
    @Override
    public TermFactory getTermFactory() {
        return termBuilder.tf();
    }

    public ITermProgramVariableCollectorFactory getFactory() {
        return factory;
    }

    public void setFactory(ITermProgramVariableCollectorFactory factory) {
        this.factory = factory;
    }


    // =================================================================================================================
    // =================================================================================================================

    // Origin label specific methods; these should eventually be moved out of the services class
    // when doing that we must take care not to introduce dependencies to ProofSettings or similar
    // in places
    // where that should not occur

    /**
     * sets the factory for origin term labels
     *
     * @param originFactory the {@link OriginTermLabelFactory} to use, if null is passed, origin
     *        labels should not be created
     */
    public void setOriginFactory(OriginTermLabelFactory originFactory) {
        this.originFactory = originFactory;
    }

    /**
     * return the factory for origin term labels
     *
     * @return the OriginTermLabelFactory to use or null if origin labels should not be created
     */
    public OriginTermLabelFactory getOriginFactory() {
        return originFactory;
    }
    // =================================================================================================================
    // =================================================================================================================

    // TODO: Ask weigl whether this is still needed
    public Lookup createLookup() {
        Lookup lookup = new Lookup();
        lookup.register(getJavaInfo());
        lookup.register(getJavaModel());
        lookup.register(getProfile());
        lookup.register(getProof());
        lookup.register(getNamespaces());
        lookup.register(getTermBuilder());
        lookup.register(getVariableNamer());
        return lookup;
    }

    @NonNull
    public JavaService getJavaService() {
        assert javaService != null : "Java Services needs to initialized in advanced.";
        return javaService;
    }

    /**
     * @return the {@link JavaService}, or {@code null} if Java was never activated for this
     *         {@link Services} (e.g. a pure first-order proof). Unlike {@link #getJavaService()}
     *         this never asserts and is safe to call during disposal.
     */
    public @Nullable JavaService getJavaServiceOrNull() {
        return javaService;
    }

    private JavaService activateJavaPath(@NonNull Path bootClassPath,
            @NonNull Collection<Path> libraryPaths, FileRepo fileRepo) {
        if (javaService != null && javaService.getBootClassPath().equals(bootClassPath)
                && CollectionUtil.containsSame(javaService.getLibraryPath(), libraryPaths)) {
            return javaService;
        }
        LOGGER.info("activate java with {} and {}", bootClassPath, libraryPaths);
        javaService = new JavaService(this, bootClassPath, libraryPaths, fileRepo);
        javaInfo = new JavaInfo(new KeYProgModelInfo(javaService), this);
        return javaService;
    }

    public JavaService activateJava(@Nullable Path bootClassPath,
            @NonNull Collection<Path> libraryPaths, FileRepo fileRepo) {
        Path path;
        if (bootClassPath != null) {
            path = bootClassPath;
        } else {
            path = getReduxPath();
        }

        if (libraryPaths == null) {
            libraryPaths = Collections.emptyList();
        }

        return activateJavaPath(path, libraryPaths, fileRepo);
    }

    public void activateJava(@Nullable Path bootClassPath) {
        activateJava(bootClassPath, Collections.emptyList(), null);
    }

    public static Path getReduxPath() {
        // TODO weigl: where to put this code. The implementation of services.getProfile() is
        // stupid.
        var resourcePath = "JavaRedux/JAVALANG.TXT";
        var url = KeYResourceManager.getManager().getResourceFile(JavaService.class, resourcePath);
        try {
            return Paths.get(url.toURI()).getParent();
        } catch (URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }
}
