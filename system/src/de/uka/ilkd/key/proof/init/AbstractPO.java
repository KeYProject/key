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
import java.util.Properties;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
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

    protected final TermBuilder tb; 
    protected final InitConfig environmentConfig;
    protected final Services environmentServices;
    protected final JavaInfo javaInfo;
    protected final HeapLDT heapLDT;
    protected final SpecificationRepository specRepos;
    protected final String name;
    protected ImmutableSet<NoPosTacletApp> taclets;
    private String header;
    private ProofAggregate proofAggregate;
    protected Term[] poTerms;
    protected String[] poNames;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    public AbstractPO(InitConfig initConfig,
                      String name) {
        this.environmentConfig = initConfig;
        this.environmentServices = initConfig.getServices();
        this.tb = environmentServices.getTermBuilder();
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
            if (axiom.getTarget()==null || !(axiom.getTarget().equals(usedObs.second)
                  && usedObs.first.extendsTrans(axiom.getKJT().getSort()))) {
                axioms = axioms.remove(axiom);
            }
        }
        return axioms;
    }


    private boolean reach(Pair<Sort, IObserverFunction> from,
                          Pair<Sort, IObserverFunction> to,
                          ImmutableSet<ClassAxiom> axioms,
                          Services services) {
        ImmutableSet<Pair<Sort, IObserverFunction>> reached =
                DefaultImmutableSet.nil();
        ImmutableSet<Pair<Sort, IObserverFunction>> newlyReached =
                DefaultImmutableSet.<Pair<Sort, IObserverFunction>>nil().add(from);

        while (!newlyReached.isEmpty()) {
            for (Pair<Sort, IObserverFunction> node : newlyReached) {
                newlyReached = newlyReached.remove(node);
                reached = reached.add(node);
                final ImmutableSet<ClassAxiom> nodeAxioms = getAxiomsForObserver(
                        node, axioms);
                for (ClassAxiom nodeAxiom : nodeAxioms) {
                    final ImmutableSet<Pair<Sort, IObserverFunction>> nextNodes =
                            nodeAxiom.getUsedObservers(services);
                    for (Pair<Sort, IObserverFunction> nextNode : nextNodes) {
                        if (nextNode.equals(to)) {
                            return true;
                        } else if (!reached.contains(nextNode)) {
                            newlyReached = newlyReached.add(nextNode);
                        }
                    }
                }
            }
        }

        return false;
    }


    private ImmutableSet<Pair<Sort, IObserverFunction>> getSCC(ClassAxiom startAxiom,
                                                               ImmutableSet<ClassAxiom> axioms,
                                                               Services services) {
        //TODO: make more efficient
        final Pair<Sort, IObserverFunction> start =
                new Pair<Sort, IObserverFunction>(startAxiom.getKJT().getSort(),
                                                  startAxiom.getTarget());
        ImmutableSet<Pair<Sort, IObserverFunction>> result =
                DefaultImmutableSet.nil();
        for (ClassAxiom nodeAxiom : axioms) {
            final Pair<Sort, IObserverFunction> node =
                    new Pair<Sort, IObserverFunction>(
                    nodeAxiom.getKJT().getSort(),
                                                     nodeAxiom.getTarget());
            if (reach(start, node, axioms, services) && reach(node, start, axioms, services)) {
                result = result.add(node);
            }
        }
        return result;
    }

    /**
     * Generate well-definedness taclets to resolve formulas as
     * WD(pv.<inv>) or WD(pv.m(...)).
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
        final ImmutableSet<ClassAxiom> axioms = selectClassAxioms(selfKJT);
        for (ClassAxiom axiom : axioms) {
            final ImmutableSet<Pair<Sort, IObserverFunction>> scc =
                    getSCC(axiom, axioms, proofConfig.getServices());
            
            for (Taclet axiomTaclet : axiom.getTaclets(scc, proofConfig.getServices())) {
                assert axiomTaclet != null : "class axiom returned null taclet: "
                        + axiom.getName();
                // only include if choices are appropriate
                if (choicesApply(axiomTaclet, proofConfig.getActivatedChoices())) {
                    register(axiomTaclet, proofConfig);
                }
            }
        }
    }

    /** Check whether a taclet conforms with the currently active choices.
     * I.e., whether the taclet's given choices is a subset of <code>choices</code>.
     */
    private boolean choicesApply (Taclet taclet, ImmutableSet<Choice> choices) {
        for (Choice tacletChoices: taclet.getChoices())
            if (!choices.contains(tacletChoices)) return false;
        return true;
    }


    private void register(Taclet t, InitConfig proofConfig) {
        assert t != null;
        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(t));
        proofConfig.registerRule(t, AxiomJustification.INSTANCE);
    }


    protected final void register(ProgramVariable pv, Services services) {
         Namespace progVarNames = services.getNamespaces().programVariables();
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
         Namespace functionNames = services.getNamespaces().functions();
         if (f != null && functionNames.lookup(f.name()) == null) {
             assert f.sort() != Sort.UPDATE;
             if (f.sort() == Sort.FORMULA) {
                 functionNames.addSafely(f);
             } else {
                 functionNames.addSafely(f);
             }
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
            sb.append("\\classpath \"").append(classPath).append("\";\n\n");
        }

        //javaSource
        sb.append("\\javaSource \"").append(javaPath).append("\";\n\n");

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
     */
    private Proof createProof(String proofName,
                              Term poTerm,
                              InitConfig proofConfig) {
        final JavaModel javaModel = proofConfig.getServices().getJavaModel();
        createProofHeader(javaModel.getModelDir(),
                          javaModel.getClassPath(),
                          javaModel.getBootClassPath(),
                          proofConfig.getServices());
        Proof proof = new Proof(proofName,
                                poTerm,
                                header,
                                proofConfig.createTacletIndex(),
                                proofConfig.createBuiltInRuleIndex(),
                                proofConfig );
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
        	if(i>0) { ic = ic.deepCopy(); }
            proofs[i] = createProof(poNames != null ? poNames[i] : name,
                                    poTerms[i], ic);
            if (taclets != null) {
                proofs[i].getGoal(proofs[i].root()).indexOfTaclets().addTaclets(
                        taclets);
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
        properties.setProperty(IPersistablePO.PROPERTY_CLASS, getClass().getCanonicalName());
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
}
