// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.List;
import java.util.Properties;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassWellDefinedness;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.MethodWellDefinedness;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.Pair;


/**
 * An abstract proof obligation implementing common functionality.
 */
public abstract class AbstractPO implements IPersistablePO {

    protected TermBuilder tb;
    protected final InitConfig environmentConfig;
    protected Services environmentServices;
    protected final JavaInfo javaInfo;
    protected final HeapLDT heapLDT;
    protected final SpecificationRepository specRepos;
    protected final String name;
    protected ImmutableSet<NoPosTacletApp> taclets;
    protected Term[] poTerms;
    protected String[] poNames;
    private String header;
    private ProofAggregate proofAggregate;


    // fields used by Tarjan Algorithm
    private HashMap<Vertex, ImmutableList<Pair<Sort, IObserverFunction>>> allSCCs = new HashMap<>();
    private final HashMap<Pair<Sort, IObserverFunction>, Vertex> vertices = new HashMap<>();
    private final ArrayDeque<Vertex> stack = new ArrayDeque<>();


    /** number of currently visited nodes */
    private int index = 0;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    public AbstractPO(InitConfig initConfig,
                      String name) {
        this.environmentConfig = initConfig;
        this.environmentServices = initConfig.getServices();
        this.javaInfo = initConfig.getServices().getJavaInfo();
        this.heapLDT = initConfig.getServices().getTypeConverter().getHeapLDT();
        this.specRepos = initConfig.getServices().getSpecificationRepository();
        this.name = name;
        taclets = DefaultImmutableSet.nil();
    }


    //-------------------------------------------------------------------------
    //methods for use in subclasses
    //-------------------------------------------------------------------------
    private ImmutableSet<ClassAxiom> getAxiomsForObserver(
            Pair<Sort, IObserverFunction> usedObs,
            ImmutableSet<ClassAxiom> axioms) {
        for (ClassAxiom axiom : axioms) {
            if (axiom.getTarget() == null || !(axiom.getTarget().equals(usedObs.second)
                  && usedObs.first.extendsTrans(axiom.getKJT().getSort()))) {
                axioms = axioms.remove(axiom);
            }
        }
        return axioms;
    }

    /**
     * Generate well-definedness taclets to resolve formulas as
     * WD(pv.{@literal <inv>}) or WD(pv.m(...)).
     * @param proofConfig the proof configuration
     */
    void generateWdTaclets(InitConfig proofConfig) {
        if (!WellDefinednessCheck.isOn()) {
            return;
        }
        ImmutableSet<RewriteTaclet> res = DefaultImmutableSet.<RewriteTaclet>nil();
        ImmutableSet<String> names = DefaultImmutableSet.<String>nil();
        for (WellDefinednessCheck ch: specRepos.getAllWdChecks()) {
            if (ch instanceof MethodWellDefinedness) {
                MethodWellDefinedness mwd = (MethodWellDefinedness)ch;
                // WD(callee.m(...))
                RewriteTaclet mwdTaclet = mwd.createOperationTaclet(proofConfig.getServices());
                String tName = mwdTaclet.name().toString();
                final String prefix;
                if (tName.startsWith(WellDefinednessCheck.OP_TACLET)) {
                    prefix = WellDefinednessCheck.OP_TACLET;
                } else if (tName.startsWith(WellDefinednessCheck.OP_EXC_TACLET)) {
                    prefix = WellDefinednessCheck.OP_EXC_TACLET;
                } else {
                    prefix = "";
                }
                tName = tName.replace(prefix, "");
                if (names.contains(tName)) {
                    for(RewriteTaclet t: res) {
                        if (t.find().toString().equals(mwdTaclet.find().toString())) {
                            res = res.remove(t);
                            names = names.remove(tName);
                            mwdTaclet = mwd.combineTaclets(t, mwdTaclet, proofConfig.getServices());
                        }
                    }
                }
                res = res.add(mwdTaclet);
                names = names.add(tName);
            }
        }
        // WD(a.<inv>)
        res = res.union(ClassWellDefinedness.createInvTaclet(proofConfig.getServices()));
        for (RewriteTaclet t: res) {
            register(t, proofConfig);
        }
    }

    protected ImmutableSet<ClassAxiom> selectClassAxioms(KeYJavaType selfKJT) {
        return specRepos.getClassAxioms(selfKJT);
    }


    protected void collectClassAxioms(KeYJavaType selfKJT, InitConfig proofConfig) {
        registerClassAxiomTaclets(selfKJT, proofConfig);
    }

    /** Check whether a taclet conforms with the currently active choices.
     * I.e., whether the taclet's given choices is a subset of <code>choices</code>.
     */
    private boolean choicesApply (Taclet taclet, ImmutableSet<Choice> choices) {
        for (Choice tacletChoices: taclet.getChoices()) {
            if (!choices.contains(tacletChoices)) {
                return false;
            }
        }
        return true;
    }


    private void register(Taclet t, InitConfig proofConfig) {
        assert t != null;
        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(t));
        proofConfig.registerRule(t, AxiomJustification.INSTANCE);
    }


    protected final void register(ProgramVariable pv, Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    protected final void register(ImmutableList<ProgramVariable> pvs, Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    protected final void register(Function f, Services services) {
        Namespace<Function> functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            if (f.sort() == Sort.FORMULA) {
                functionNames.addSafely(f);
            } else {
                functionNames.addSafely(f);
            }
        }
    }

    /**
     * Generates the general assumption that self is not null.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfNotNull(IProgramMethod pm, ProgramVariable selfVar) {
        return selfVar == null || pm.isConstructor() ?
                tb.tt() :
                    tb.not(tb.equals(tb.var(selfVar), tb.NULL()));
    }

    /**
     * Generates the general assumption that self is created.
     * @param heaps The heap context
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param services The services instance.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfCreated(List<LocationVariable> heaps, IProgramMethod pm,
            ProgramVariable selfVar, Services services) {
        if(selfVar == null || pm.isConstructor()) {
            return tb.tt();
        }
        Term created = null;
        for(LocationVariable heap : heaps) {
            if (heap == services.getTypeConverter().getHeapLDT().getSavedHeap()) {
                continue;
            }
            final Term cr = tb.created(tb.var(heap), tb.var(selfVar));
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
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfExactType(IProgramMethod pm,
                                         ProgramVariable selfVar,
                                         KeYJavaType selfKJT) {
        return selfVar == null || pm.isConstructor()
                ? tb.tt() : generateSelfExactType(pm, tb.var(selfVar), selfKJT);
    }

    /**
     * Generates the general assumption which defines the type of self.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfExactType(IProgramMethod pm,
                                         Term selfVar,
                                         KeYJavaType selfKJT) {
        final Term selfExactType =
                selfVar == null || pm.isConstructor() ?
                        tb.tt()
                        : tb.exactInstance(selfKJT.getSort(), selfVar);
        return selfExactType;
    }

    // ==================================================
    // Implementation of Tarjan algorithm to compute SCC
    // ==================================================

    /**
     * Represents a vertex and additional information required by the Tarjan algorithm.
     * Two vertices are equal if the observer function and the target sort are identical.
     */
    static class Vertex {

        /** to avoid linear lookup in the stack */
        boolean onStack;

        /** the index (number of already visited nodes) and -1 if not yet visited */
        int index;

        /** an SCC is identified by the node that was visited first */
        int lowLink;

        private final ClassAxiom axiom;
        private final Pair<Sort, IObserverFunction> core;

        public Vertex(Pair<Sort, IObserverFunction> vertexCore,
                      ClassAxiom axiom, boolean onStack,
                      int index, int lowLink) {
            this.core = vertexCore;
            this.axiom = axiom;
            this.onStack = onStack;
            this.index = index;
            this.lowLink = lowLink;
        }

        public boolean equals(Object o) {
            if (o instanceof Vertex) {
                Vertex other = (Vertex) o;
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
     *
     * @param selfKJT the {@link KeYJavaType} for which to collect all accessible class axioms
     * @param proofConfig the {@link InitConfig} of the proof for this PO
     */
    private void registerClassAxiomTaclets(KeYJavaType selfKJT, InitConfig proofConfig) {
        final ImmutableSet<ClassAxiom> axioms = selectClassAxioms(selfKJT);
        for (ClassAxiom axiom : axioms) {
            final Vertex node = getVertexFor(axiom.getKJT().getSort(), axiom.getTarget(), axiom);
            if (node.index == -1) {
                getSCCForNode(node, axioms, proofConfig);
            }
            ImmutableList<Pair<Sort, IObserverFunction>> scc = allSCCs.get(node);
            for (Taclet axiomTaclet :
                axiom.getTaclets(DefaultImmutableSet.fromImmutableList(scc == null ?
                        ImmutableSLList.<Pair<Sort, IObserverFunction>>nil() : scc),
                        proofConfig.getServices())) {
                assert axiomTaclet != null : "class axiom returned null taclet: "
                        + axiom.getName();
                // only include if choices are appropriate
                if (choicesApply(axiomTaclet, proofConfig.getActivatedChoices())) {
                    register(axiomTaclet, proofConfig);
                }
            }
        }

        index = 0;
        stack.clear();
        vertices.clear();
        allSCCs.clear();
    }

    /**
     * computes all strongly connected components reachable by the given node and adds them
     * to {@link AbstractPO#allSCCs}
     *
     * @param node the starting {@link Vertex}
     * @param axioms set of {@link ClassAxiom} used to compute the outgoing edges of the nodes
     * @param proofConfig the {@link InitConfig} of the proof for this PO
     */
    private void getSCCForNode(final Vertex node,
                               ImmutableSet<ClassAxiom> axioms,
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
                    ImmutableSLList.<Pair<Sort, IObserverFunction>>nil();
            Vertex sccMember;
            do  {
                sccMember = stack.pop();
                sccMember.onStack = false;
                scc = scc.prepend(sccMember.core);
            } while(!sccMember.equals(node));
            allSCCs.put(node, scc);
        }
    }




    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    @Override
    public final String name() {
        return name;
    }


    /**
     * Creates declarations necessary to save/load proof in textual form
     * (helper for createProof()).
     */
    private void createProofHeader(String javaPath,
            String classPath,
            String bootClassPath,
            String includedFiles,
            Services services) {
        if (header != null) {
            return;
        }
        final StringBuffer sb = new StringBuffer();

        //bootclasspath
        if (bootClassPath != null && !bootClassPath.equals("")) {
            sb.append("\\bootclasspath \"").append(bootClassPath).append(
                    "\";\n\n");
        }

        //classpath
        if (classPath != null && !classPath.equals("")) {
            sb.append("\\classpath ").append(classPath).append(";\n\n");
        }

        //javaSource
        sb.append("\\javaSource \"").append(javaPath).append("\";\n\n");

        //include
        if (includedFiles != null && !includedFiles.equals("")) {
            sb.append("\\include ").append(includedFiles).append(";\n\n");
        }

        //contracts
        ImmutableSet<Contract> contractsToSave = specRepos.getAllContracts();
        for (Contract c : contractsToSave) {
            if (!c.toBeSaved()) {
                contractsToSave = contractsToSave.remove(c);
            }
        }
        if (!contractsToSave.isEmpty()) {
            sb.append("\\contracts {\n");
            for (Contract c : contractsToSave) {
                sb.append(c.proofToString(services));
            }
            sb.append("}\n\n");
        }

        header = sb.toString();
    }


    /**
     * Creates a Proof (helper for getPO()).
     * @param proofName name of the proof
     * @param poTerm term of the proof obligation
     * @param proofConfig the proof configuration
     * @return the created proof
     */
    protected Proof createProof(String proofName,
            Term poTerm,
            InitConfig proofConfig) {
        if (proofConfig == null) {
            proofConfig = environmentConfig.deepCopy();
        }
        final JavaModel javaModel = proofConfig.getServices().getJavaModel();
        createProofHeader(javaModel.getModelDir(),
                javaModel.getClassPath(),
                javaModel.getBootClassPath(),
                javaModel.getIncludedFiles(),
                proofConfig.getServices());

        final Proof proof = createProofObject(proofName, header, poTerm, proofConfig);

        assert proof.openGoals().size() == 1 : "expected one first open goal";
        return proof;
    }


    protected Proof createProofObject(String proofName, String proofHeader, Term poTerm,
            InitConfig proofConfig) {
        Proof proof = new Proof(proofName,
                poTerm,
                proofHeader,
                proofConfig);
        return proof;
    }


    protected abstract InitConfig getCreatedInitConfigForSingleProof();

    @Override
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
            proofs[i] =
                    createProof(poNames != null ? poNames[i] : name,
                                poTerms[i], ic);
            if (taclets != null) {
                proofs[i].getGoal(proofs[i].root())
                        .indexOfTaclets().addTaclets(taclets);
            }
        }

        proofAggregate = ProofAggregate.createProofAggregate(proofs, name);
        return proofAggregate;
    }


    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }


    protected void assignPOTerms(Term... poTerms) {
        this.poTerms = poTerms;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        properties.setProperty(IPersistablePO.PROPERTY_CLASS,
                               getClass().getCanonicalName());
        properties.setProperty(IPersistablePO.PROPERTY_NAME, name);
    }

    /**
     * Returns the name value from the given properties.
     * @param properties The properties to read from.
     * @return The name value.
     */
    public static String getName(Properties properties) {
        return properties.getProperty(IPersistablePO.PROPERTY_NAME);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return null;
    }
}
