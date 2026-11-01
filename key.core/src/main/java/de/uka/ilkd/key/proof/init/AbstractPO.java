/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.init;

import java.util.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.*;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * An abstract proof obligation implementing common functionality.
 *
 * <p>
 * The {@link #tb} field is assigned by {@code postInit()} in every subclass before any of the
 * proof-obligation building steps run (each subclass invokes {@code postInit()} at the very
 * beginning of its {@code readProblem()}); it is never read before that assignment. It is declared
 * {@code @Nullable} since it cannot be assigned in the constructor -- the term builder has to be
 * built from the proof-specific {@link Services} that {@code postInit()} derives. The dereferences
 * of {@code tb} in these helpers are therefore suppressed with scoped keys.
 */
@NullMarked
public abstract class AbstractPO implements IPersistablePO {

    protected @Nullable TermBuilder tb;
    protected final InitConfig environmentConfig;
    protected Services environmentServices;
    protected final JavaInfo javaInfo;
    protected final HeapLDT heapLDT;
    protected final SpecificationRepository specRepos;
    protected final String name;
    protected ImmutableSet<NoPosTacletApp> taclets;
    protected @Nullable JTerm[] poTerms;
    protected @Nullable String[] poNames;
    private KeyAst.@Nullable Declarations header;
    private @Nullable ProofAggregate proofAggregate;


    // fields used by Tarjan Algorithm
    private final HashMap<Vertex, ImmutableList<Pair<Sort, IObserverFunction>>> allSCCs =
        new HashMap<>();
    private final HashMap<Pair<Sort, IObserverFunction>, Vertex> vertices = new HashMap<>();
    private final ArrayDeque<Vertex> stack = new ArrayDeque<>();


    /**
     * number of currently visited nodes
     */
    private int index = 0;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------
    /**
     * The proof-obligation terms are produced by {@code assignPOTerms(JTerm...)} after construction
     * (and are {@code @Nullable} until then); the difference is suppressed with a scoped key. The
     * heap LDT of a fully configured {@link InitConfig} is always present (it is part of the JavaDL
     * theory, see the assertion in {@code ProblemInitializer}); the lookups below and the resulting
     * assignments into final fields are suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:initialization.fields.uninitialized",
        "nullness:assignment.type.incompatible" })
    protected AbstractPO(InitConfig initConfig, String name) {
        this.environmentConfig = initConfig;
        this.environmentServices = initConfig.getServices();
        this.javaInfo = initConfig.getServices().getJavaInfo();
        this.heapLDT = initConfig.getServices().getTypeConverter().getHeapLDT();
        this.specRepos = initConfig.getServices().getSpecificationRepository();
        this.name = name;
        taclets = DefaultImmutableSet.nil();
    }


    // -------------------------------------------------------------------------
    // methods for use in subclasses
    // -------------------------------------------------------------------------
    private ImmutableSet<ClassAxiom> getAxiomsForObserver(Pair<Sort, IObserverFunction> usedObs,
            ImmutableSet<ClassAxiom> axioms) {
        for (ClassAxiom axiom : axioms) {
            final @Nullable IObserverFunction target = axiom.getTarget();
            final @Nullable Sort axiomSort = axiom.getKJT().getSort();
            // an axiom without a concrete sort cannot stand in an observer-extension relation, so
            // it is treated like an axiom without a matching target: not part of the set
            if (target == null || axiomSort == null || !(target.equals(usedObs.second)
                    && usedObs.first.extendsTrans(axiomSort))) {
                axioms = axioms.remove(axiom);
            }
        }
        return axioms;
    }

    /// Queries the registered (dynamic) taclet generators.
    /// The taclet generator receives the `initConfig` to add further taclets to the proof.
    /// @see TacletPOGenerator
    protected void generateDynamicTaclets(InitConfig initConfig) {
        var generators = ServiceLoader.load(TacletPOGenerator.class);
        generators.forEach(it -> it.generate(this, initConfig, specRepos));
    }


    protected ImmutableSet<ClassAxiom> selectClassAxioms(KeYJavaType selfKJT) {
        return specRepos.getClassAxioms(selfKJT);
    }


    protected void collectClassAxioms(KeYJavaType selfKJT, InitConfig proofConfig) {
        registerClassAxiomTaclets(selfKJT, proofConfig);
    }

    public void register(Taclet t, InitConfig proofConfig) {
        assert t != null;
        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(t));
        proofConfig.registerRule(t, AxiomJustification.INSTANCE);
    }


    protected final void register(@Nullable LocationVariable pv, Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    protected final void register(ImmutableList<LocationVariable> pvs, Services services) {
        for (LocationVariable pv : pvs) {
            register(pv, services);
        }
    }


    protected final void register(@Nullable Function f, Services services) {
        Namespace<Function> functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != JavaDLTheory.UPDATE;
            functionNames.addSafely(f);
        }
    }

    /**
     * Generates the general assumption that self is not null.
     *
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    /**
     * The {@link #tb} term builder is assigned by {@code postInit()} before this helper is invoked
     * (see the class level invariant documentation), so its dereference here is suppressed with a
     * scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected JTerm generateSelfNotNull(IProgramMethod pm, @Nullable ProgramVariable selfVar) {
        return selfVar == null || pm.isConstructor() ? tb.tt()
                : tb.not(tb.equals(tb.var(selfVar), tb.NULL()));
    }

    /**
     * Generates the general assumption that self is created.
     *
     * @param heaps The heap context
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param services The services instance.
     * @return The term representing the general assumption.
     */
    /**
     * The accumulator is {@code @Nullable} during the build; the invariants of the method guarantee
     * a non-null result, so the difference is suppressed with a scoped key. The {@link #tb} term
     * builder and the heap LDT are guaranteed by the {@code postInit()} contract as documented at
     * the field declaration, so their dereferences are suppressed with scoped keys too.
     */
    @SuppressWarnings({ "nullness:return.type.incompatible", "nullness:dereference.of.nullable" })
    protected JTerm generateSelfCreated(List<LocationVariable> heaps, IProgramMethod pm,
            @Nullable ProgramVariable selfVar, Services services) {
        if (selfVar == null || pm.isConstructor()) {
            return tb.tt();
        }
        JTerm created = null;
        for (LocationVariable heap : heaps) {
            if (heap == services.getTypeConverter().getHeapLDT().getSavedHeap()) {
                continue;
            }
            final JTerm cr = tb.created(tb.var(heap), tb.var(selfVar));
            if (created == null) {
                created = cr;
            } else {
                created = tb.and(created, cr);
            }
        }
        return created;
    }


    /**
     * Generates the general assumption which defines the type of self.
     *
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    /**
     * The {@link #tb} term builder is assigned by {@code postInit()} before this helper is invoked
     * (see the field declaration), so its dereference here is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected JTerm generateSelfExactType(IProgramMethod pm, @Nullable ProgramVariable selfVar,
            KeYJavaType selfKJT) {
        return selfVar == null || pm.isConstructor() ? tb.tt()
                : generateSelfExactType(pm, tb.var(selfVar), selfKJT);
    }

    /**
     * Generates the general assumption which defines the type of self.
     *
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    /**
     * The {@link #tb} term builder is assigned by {@code postInit()} before this helper is invoked
     * (see the field declaration); the lookups of the self type and its sort below are guaranteed
     * to be present for the receiver type of a program method. The differences are suppressed with
     * scoped keys.
     */
    @SuppressWarnings({ "nullness:argument.type.incompatible", "nullness:dereference.of.nullable" })
    protected JTerm generateSelfExactType(IProgramMethod pm, @Nullable JTerm selfVar,
            KeYJavaType selfKJT) {
        return selfVar == null || pm.isConstructor() ? tb.tt()
                : tb.exactInstance(selfKJT.getSort(), selfVar);
    }

    // ==================================================
    // Implementation of Tarjan algorithm to compute SCC
    // ==================================================

    /**
     * Represents a vertex and additional information required by the Tarjan algorithm. Two vertices
     * are equal if the observer function and the target sort are identical.
     */
    static class Vertex {

        /**
         * to avoid linear lookup in the stack
         */
        boolean onStack;

        /**
         * the index (number of already visited nodes) and -1 if not yet visited
         */
        int index;

        /**
         * an SCC is identified by the node that was visited first
         */
        int lowLink;

        private final ClassAxiom axiom;
        private final Pair<Sort, IObserverFunction> core;

        public Vertex(Pair<Sort, IObserverFunction> vertexCore, ClassAxiom axiom, boolean onStack,
                int index, int lowLink) {
            this.core = vertexCore;
            this.axiom = axiom;
            this.onStack = onStack;
            this.index = index;
            this.lowLink = lowLink;
        }

        public boolean equals(@Nullable Object o) {
            if (o instanceof Vertex other) {
                return core.equals(other.core);
            } else {
                return false;
            }
        }

        public int hashCode() {
            return 17 * core.hashCode();
        }

        ClassAxiom getAxiom() {
            return axiom;
        }
    }

    private Vertex getVertexFor(Sort targetSort, IObserverFunction observer, ClassAxiom axiom) {
        final Pair<Sort, IObserverFunction> vertexCore = new Pair<>(targetSort, observer);
        Vertex vertex = vertices.get(vertexCore);
        if (vertex == null) {
            vertex = new Vertex(vertexCore, axiom, false, -1, -1);
            vertices.put(vertexCore, vertex);
        }
        return vertex;
    }

    private Vertex getVertexFor(Pair<Sort, IObserverFunction> vertexCore, ClassAxiom axiom) {
        Vertex vertex = vertices.get(vertexCore);
        if (vertex == null) {
            vertex = new Vertex(vertexCore, axiom, false, -1, -1);
            vertices.put(vertexCore, vertex);
        }
        return vertex;
    }


    /**
     * adds all taclets for the class axioms accessible and needed by this PO
     * <p>
     * The vertex graph is keyed on the pair (sort, target observer) of a class axiom; class axioms
     * do not have a target (see {@code ClassAxiom#getTarget()}, whose implementation always
     * returns {@code null}), so the {@link #getVertexFor(Sort, IObserverFunction, ClassAxiom)}
     * arguments are the (nullable) lookups without an intermediate guard, suppressed with a scoped
     * key.
     *
     * @param selfKJT the {@link KeYJavaType} for which to collect all accessible class axioms
     * @param proofConfig the {@link InitConfig} of the proof for this PO
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private void registerClassAxiomTaclets(KeYJavaType selfKJT, InitConfig proofConfig) {
        final ImmutableSet<ClassAxiom> axioms = selectClassAxioms(selfKJT);
        for (ClassAxiom axiom : axioms) {
            final Vertex node = getVertexFor(axiom.getKJT().getSort(), axiom.getTarget(), axiom);
            if (node.index == -1) {
                getSCCForNode(node, axioms, proofConfig);
            }
            ImmutableList<Pair<Sort, IObserverFunction>> scc = allSCCs.get(node);
            for (Taclet axiomTaclet : axiom.getTaclets(
                DefaultImmutableSet.fromImmutableList(
                    scc == null ? ImmutableList.nil() : scc),
                proofConfig.getServices())) {
                assert axiomTaclet != null : "class axiom returned null taclet: " + axiom.getName();
                // only include if choices are appropriate
                // weigl: register always! choices are evaluated as late as possible.
                // This would technically allow to change Taclet options after loading.
                register(axiomTaclet, proofConfig);
            }
        }

        index = 0;
        stack.clear();
        vertices.clear();
        allSCCs.clear();
    }

    /**
     * computes all strongly connected components reachable by the given node and adds them to
     * {@link AbstractPO#allSCCs}
     *
     * @param node the starting {@link Vertex}
     * @param axioms set of {@link ClassAxiom} used to compute the outgoing edges of the nodes
     * @param proofConfig the {@link InitConfig} of the proof for this PO
     */
    private void getSCCForNode(final Vertex node, ImmutableSet<ClassAxiom> axioms,
            InitConfig proofConfig) {
        final Services services = proofConfig.getServices();
        node.index = index;
        node.lowLink = index;
        index++;
        stack.push(node);
        node.onStack = true;

        for (final ClassAxiom nodeAxiom : getAxiomsForObserver(node.core, axioms)) {
            final ImmutableSet<Pair<Sort, IObserverFunction>> nextNodes =
                nodeAxiom.getUsedObservers(services);
            for (Pair<Sort, IObserverFunction> nextNodeCore : nextNodes) {
                final Vertex nextNode = getVertexFor(nextNodeCore, nodeAxiom);
                if (nextNode.index == -1) {
                    getSCCForNode(nextNode, axioms, proofConfig);
                    if (node.lowLink > nextNode.lowLink) {
                        node.lowLink = nextNode.lowLink;
                    }
                } else if (nextNode.onStack) {
                    if (node.lowLink > nextNode.index) {
                        node.lowLink = nextNode.index;
                    }
                }
            }
        }

        if (node.index == node.lowLink) {
            ImmutableList<Pair<Sort, IObserverFunction>> scc =
                ImmutableList.nil();
            Vertex sccMember;
            do {
                sccMember = stack.pop();
                sccMember.onStack = false;
                scc = scc.prepend(sccMember.core);
            } while (!sccMember.equals(node));
            allSCCs.put(node, scc);
        }
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------
    @Override
    public final String name() {
        return name;
    }


    /**
     * Creates a Proof (helper for getPO()).
     *
     * @param proofName name of the proof
     * @param poTerm term of the proof obligation
     * @param proofConfig the proof configuration
     * @return the created proof
     */
    protected Proof createProof(String proofName, JTerm poTerm, @Nullable InitConfig proofConfig) {
        if (proofConfig == null) {
            proofConfig = environmentConfig.deepCopy();
        }
        header = proofConfig.getProblemHeader();

        final Proof proof = createProofObject(proofName, header, poTerm, proofConfig);

        assert proof.openGoals().size() == 1 : "expected one first open goal";
        return proof;
    }



    /**
     * Creates the {@link Proof} object for a single proof obligation.
     *
     * @param proofName the name of the proof
     * @param proofHeader the user-given declarations from the problem file, or {@code null} if none
     *        were loaded (the {@link Proof} constructor accepts a nullable problem header)
     * @param poTerm the proof obligation term
     * @param proofConfig the init config of the proof
     * @return the created proof
     */
    protected Proof createProofObject(String proofName, KeyAst.@Nullable Declarations proofHeader,
            JTerm poTerm,
            InitConfig proofConfig) {
        return new Proof(proofName, poTerm, proofHeader, proofConfig);
    }


    protected abstract @Nullable InitConfig getCreatedInitConfigForSingleProof();

    @Override
    /**
     * The {@code proofAggregate} field is {@code @Nullable} only because the obligation is built
     * lazily by {@link #createPOs(String, List, InitConfig, TacletIndex)}; the caller is expected
     * to invoke that builder first, so the difference is suppressed with a scoped key. Likewise,
     * the init configuration from {@link #getCreatedInitConfigForSingleProof()} and the goal
     * lookups on the freshly created proofs are guaranteed by the {@code postInit()} contract
     * documented at the {@link #tb} field, so their dereferences are suppressed with a scoped key
     * too.
     */
    @SuppressWarnings({ "nullness:return.type.incompatible", "nullness:dereference.of.nullable" })
    public final ProofAggregate getPO() {
        if (proofAggregate != null) {
            return proofAggregate;
        }

        if (poTerms == null) {
            throw new IllegalStateException("No proof obligation terms.");
        }

        Proof[] proofs = new Proof[poTerms.length];
        InitConfig ic = getCreatedInitConfigForSingleProof();
        for (int i = 0; i < proofs.length; i++) {
            if (i > 0) {
                ic = ic.deepCopy();
            }
            final String poName = poNames != null && poNames[i] != null ? poNames[i] : name;
            // the PO terms are guaranteed by the {@code assignPOTerms(JTerm...)} contract to be
            // present and non-null once {@code getPO()} is called; the guard below only documents
            // that invariant
            final @Nullable JTerm poTerm = poTerms[i];
            if (poTerm == null) {
                throw new IllegalStateException("No proof obligation term for " + poName);
            }
            proofs[i] = createProof(poName, poTerm, ic);
            if (taclets != null) {
                var filteredTaclets = proofs[i].getInitConfig().filterTaclets(taclets);
                // the root of a freshly created proof is guaranteed to be set by its constructor;
                // the guard below only documents that invariant
                final @Nullable Node root = proofs[i].root();
                if (root != null) {
                    proofs[i].getOpenGoal(root).indexOfTaclets()
                            .addTaclets(filteredTaclets);
                }
            }
        }

        proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
        return proofAggregate;
    }


    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }


    protected void assignPOTerms(JTerm... poTerms) {
        this.poTerms = poTerms;
    }

    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = new Configuration();
        c.set(PROPERTY_CLASS, getClass().getCanonicalName());
        c.set(PROPERTY_NAME, name);
        return c;
    }

    /**
     * Returns the name value from the given properties.
     *
     * @param properties The properties to read from.
     * @return The name value.
     */
    public static @Nullable String getName(Configuration properties) {
        return properties.getString(PROPERTY_NAME);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable KeYJavaType getContainerType() {
        return null;
    }
}
