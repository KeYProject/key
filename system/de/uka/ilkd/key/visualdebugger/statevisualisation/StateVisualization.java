// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.statevisualisation;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPairImpl;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.rule.updatesimplifier.UpdateSimplifierTermFactory;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.DebuggerPO;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchPoint;

public class StateVisualization {

    private ImmutableSet<Term> arrayIndexTerms;

    private final ImmutableSet<Term> arrayLocations;

    private ImmutableSet<Term>[][] indexConfigurations;

    private ImmutableSet<Term>[] instanceConfigurations;

    private final ITNode itNode;

    private final ImmutableList<Term> locations;

    private final KeYMediator mediator;

    // IList<Term> terms = ImmSLList.<Term>nil();

    private DebuggerPO po = new DebuggerPO("DebuggerPo");

    private Term[] postAttributes;

    private ImmutableList<Term>[][] postValues;

    private PosInOccurrence programPio;

    private ProofStarter ps;

    private ImmutableSet<Term> refInPC = DefaultImmutableSet.<Term>nil();

    private final Services serv;

    private RigidFunction stateOp;

    private Term statePred;

    private TermBuilder TB = TermBuilder.DF;
    
    private VisualDebugger vd;

    private int maxProofSteps;

    private boolean useDecisionProcedures;

    public StateVisualization(ITNode itn, KeYMediator mediator, 
            int maxProofSteps, boolean useDecisionProcedures) {
        this.itNode = itn;
        this.vd = VisualDebugger.getVisualDebugger();
        this.mediator = mediator;

        this.serv = mediator.getServices();

        this.maxProofSteps = maxProofSteps;
        this.useDecisionProcedures = useDecisionProcedures;
        
        refInPC = getReferences(itNode.getPc());

        this.programPio = vd.getProgramPIO(itNode.getNode().sequent());
        if (programPio == null) {
            programPio = vd.getExecutionTerminatedNormal(itNode.getNode());
        }
        if (programPio == null)
            throw new RuntimeException("Program Pio not found in Sequent "
                    + itNode.getNode().sequent());
        
        simplifyUpdate();
        
        setUpProof(null, null);

        locations = vd.getLocations(programPio);
        arrayIndexTerms = vd.getArrayIndex(programPio);

        // getRefsInPreState(locations);
        arrayLocations = vd.getArrayLocations(programPio);
        final Term programPio2 = addRememberPrestateUpdates(programPio
                .constrainedFormula().formula());
        // statePred = this.createPredicate(locations);

        
        applyCuts(refInPC);

        computeInstanceConfigurations();
        this.indexConfigurations = new ImmutableSet[this.instanceConfigurations.length][];
        for (int i = 0; i < instanceConfigurations.length; i++) {
            setUpProof(instanceConfigurations[i], null);
            applyCuts(arrayIndexTerms);            
            computeArrayConfigurations(i);
        }

        postValues = new ImmutableList[instanceConfigurations.length][];
        for (int i = 0; i < instanceConfigurations.length; i++) {
            postValues[i] = new ImmutableList[indexConfigurations[i].length];
            for (int j = 0; j < indexConfigurations[i].length; j++) {
                setUpProof(instanceConfigurations[i]
                    .union(indexConfigurations[i][j]), programPio2);
                
                ps.run(mediator.getProof().env());
                                
                postValues[i][j] = getPostState(ps.getProof().openGoals()
                        .head().node().sequent());
            }
        }
        
        vd.fireDebuggerEvent(new DebuggerEvent(DebuggerEvent.VIS_STATE, this));
    }

    private Term addRememberPrestateUpdates(Term target) {
        Term locs[] = locations.toArray(new Term[locations.size()]);
        postAttributes = new Term[locs.length];  
        
        Update up = Update.createUpdate(target);

        LinkedList newAP = new LinkedList();
        // for(Iterator<Term> it= this.refsInPreState.iterator();it.hasNext();){
        for (int i = 0; i < locs.length; i++) {
            if (locs[i].op() instanceof AttributeOp) {
                final LocationVariable pv = new LocationVariable(
                        new ProgramElementName("pre" + i), locs[i].sub(0)
                                .sort());
                
                final Term t = TB.var(pv);
                
                postAttributes[i] = TB.dot(t, 
                        (ProgramVariable) (((AttributeOp) locs[i].op()).attribute()));

                newAP.add(new AssignmentPairImpl(pv, new Term[0], 
                        locs[i].sub(0)));
            } else if (locs[i].op() instanceof ProgramVariable) {
                postAttributes[i] = locs[i];

            } else if (locs[i].op() instanceof ArrayOp) {
                final LocationVariable pv_array_ref = new LocationVariable(
                        new ProgramElementName("pre_array_" + i), locs[i]
                                .sub(0).sort());
                final Term t = TB.var(pv_array_ref);

                newAP.add(new AssignmentPairImpl(pv_array_ref, new Term[0],
                        locs[i].sub(0)));

                final LocationVariable pv_index = new LocationVariable(
                        new ProgramElementName("pre_array_index_" + i), locs[i]
                                .sub(1).sort());

                final Term indexT = TB.var(pv_index);
                newAP.add(new AssignmentPairImpl(pv_index, new Term[0], locs[i]
                        .sub(1)));

                postAttributes[i] = TB.array(t, indexT);
            }

        }

        ImmutableArray<AssignmentPair> apOld = up.getAllAssignmentPairs();
        AssignmentPair[] aps = new AssignmentPair[newAP.size() + apOld.size()];

        for (int i = newAP.size(); i < apOld.size() + newAP.size(); i++) {
            aps[i] = apOld.get(i - newAP.size());
        }

        for (int i = 0; i < newAP.size(); i++) {
            aps[i] = (AssignmentPair) newAP.get(i); // TODO

        }

        statePred = createPredicate(ImmutableSLList.<Term>nil()
                .append(postAttributes));

        return UpdateSimplifierTermFactory.DEFAULT.createUpdateTerm(aps,
                this.statePred);

    }

    private synchronized void applyCutAndRun(ImmutableList<Goal> goals, Term inst) {
        for (Iterator<Goal> it = goals.iterator(); it.hasNext();) {
            final Goal g = it.next();
            final NoPosTacletApp c = g.indexOfTaclets().lookup("cut");
            assert c != null;
            // c.
            ImmutableSet<SchemaVariable> set2 = c.neededUninstantiatedVars();
            SchemaVariable cutF = set2.iterator().next();

            TacletApp t2 = c.addInstantiation(cutF, inst, false);

            g.apply(t2);

            ps.run(mediator.getProof().env());
        }

    }

    private void applyCuts(ImmutableSet<Term> terms) {
        Term[] t1 = terms.toArray(new Term[terms.size()]);
        Term[] t2 = terms.toArray(new Term[terms.size()]);

        for (int i1 = 0; i1 < t1.length; i1++) {
            for (int i2 = i1; i2 < t2.length; i2++) {
                if (!t1[i1].equals(t2[i2])) {
                    if (t1[i1].sort().extendsTrans(t2[i2].sort())
                            || t2[i2].sort().extendsTrans(t1[i1].sort())) {                       
                        applyCutAndRun(ps.getProof().openGoals(), 
                                TB.equals(t1[i1], t2[i2]));
                    }
                }
            }
        }
    }

    private void computeArrayConfigurations(int instanceConf) {
        final HashSet indexConf = new HashSet();
        
        final Proof proof = ps.getProof();
        final Node root = proof.root();
        for (Iterator<Goal> it = proof.openGoals().iterator(); it.hasNext();) {
            indexConf.add(getAppliedCutsSet(it.next().node(), root));
        }
        this.indexConfigurations[instanceConf] = new ImmutableSet[indexConf.size()];
        int i = 0;
        for (Iterator it = indexConf.iterator(); it.hasNext(); i++) {
            indexConfigurations[instanceConf][i] = (ImmutableSet<Term>) it.next();           
        }

    }

    private void computeInstanceConfigurations() {
        HashSet indexConf = new HashSet();

        final Proof proof = ps.getProof();
        final Node root = proof.root();
        for (Iterator<Goal> it = proof.openGoals().iterator(); it.hasNext();) {
            indexConf.add(getAppliedCutsSet(it.next().node(), root));
        }
        this.instanceConfigurations = new ImmutableSet[indexConf.size()];
        int i = 0;
        for (Iterator it = indexConf.iterator(); it.hasNext();i++) {
            instanceConfigurations[i] = (ImmutableSet<Term>) it.next();
        }

    }

    private Term createPredicate(ImmutableList<Term> locs) {
        Term result = null;

        final Sort[] s = new Sort[locs.size()];
        final Term[] locsArray = new Term[locs.size()];
        
        int i = 0;
        for (Term t : locs) {
            s[i] = t.sort();
            locsArray[i] = t;
            i++;
        }

        stateOp = new RigidFunction(new Name("STATE"), Sort.FORMULA, s);

        result = TermFactory.DEFAULT.createFunctionTerm(stateOp, locsArray);

        return result;
    }

    private ImmutableSet<Term> getAppliedCutsSet(Node n, Node root) {      
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        if (!root.find(n)) {
            throw new RuntimeException("node n ist not a childs of node root");
        }

        while (!(n.serialNr() == root.serialNr())) {
            final Node oldN = n;
            n = n.parent();
            if (n.getAppliedRuleApp() instanceof NoPosTacletApp) {
                NoPosTacletApp npta = (NoPosTacletApp) n.getAppliedRuleApp();
                if (npta.taclet().name().toString().toUpperCase().equals("CUT")) {
                    Term inst = (Term) npta.instantiations().lookupEntryForSV(
                            new Name("cutFormula")).value().getInstantiation();
                    if (n.child(1) == oldN)// TODO or 0
                        inst = TB.not(inst);
                    result = result.add(inst);

                }
            }
        }

        return result;

    }

    public ImmutableSet<Term>[] getPossibleIndexTermsForPcState(int i) {
        return indexConfigurations[i];

    }

    private ImmutableList<Term> getPostState(Sequent s) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (final Iterator<ConstrainedFormula> it = s.succedent().iterator(); 
             it.hasNext();) {
            final Term formula = it.next().formula();
            if (formula.op() == stateOp) {
                for (int i = 0, ar = formula.arity(); i < ar; i++) {
                    result = result.append(formula.sub(i));
                }
            }
        }
        return result;
    }

    private ImmutableSet<Term> getReferences(ImmutableList<Term> terms) {
        // IList<Term> pc = itNode.getPc();
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        for (Iterator<Term> it = terms.iterator(); it.hasNext();) {
            result = result.union(getReferences(it.next()));
        }
        return result;
    }

    private ImmutableSet<Term> getReferences(Term t) {
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        if (referenceSort(t.sort()) && t.freeVars().size() == 0)
            result = result.add(t);
        for (int i = 0; i < t.arity(); i++) {
            result = result.union(getReferences(t.sub(i)));
        }
        return result;
    }

    public SymbolicObjectDiagram getSymbolicState(int i, ImmutableSet<Term> indexTerms,
            boolean pre) {
        for (int j = 0; j < indexConfigurations[i].length; j++) {
            if (indexTerms.subset(indexConfigurations[i][j])) {
                final ImmutableList<Term> pt = postValues[i][j];
                final SymbolicObjectDiagram s = new SymbolicObjectDiagram(itNode,
                        mediator.getServices(), itNode.getPc(), refInPC,
                        locations, pt, pre, this.arrayLocations,
                        indexConfigurations[i], indexConfigurations[i][j],
                        instanceConfigurations[i]);
                return s;
            }
        }
        return null;
    }

    public int numberOfPCStates() {
        return this.instanceConfigurations.length;
    }

    private boolean referenceSort(Sort s) {
        final JavaInfo info = serv.getJavaInfo();
        final KeYJavaType kjt = info.getKeYJavaType(s);
        if (kjt == null)
            return false;
        // a ClassType represents classes, interfaces, arrays and null
        return kjt.getJavaType() instanceof ClassType;
    }

    private void initProofStarter(ProofOblInput po) {
        ps = new ProofStarter();
        ps.addProgressMonitor(VisualDebugger.getVisualDebugger().getEtProgressMonitor());
        ps.init(po);
        ps.setMaxSteps(maxProofSteps);
        ps.setUseDecisionProcedure(useDecisionProcedures);
        vd.setProofStrategy(ps.getProof(), true, false, new LinkedList<WatchPoint>());
    }
    
    private void setUpProof(ImmutableSet<Term> indexConf, Term forPostValues) {
        po = new DebuggerPO("DebuggerPo");
        if (forPostValues != null) {
            po.setUp(vd.getPrecondition(), itNode, indexConf, forPostValues);
        } else {
            if (indexConf == null) {
                po.setUp(vd.getPrecondition(), itNode);                
            } else {
                po.setUp(vd.getPrecondition(), itNode, indexConf);
            }
        }        
        final Proof proof = mediator.getProof();
        final InitConfig initConfig = proof.env().getInitConfig();
        po.setIndices(initConfig.createTacletIndex(), 
                initConfig.createBuiltInRuleIndex());
        po.setProofSettings(proof.getSettings());
        po.setConfig(initConfig);
        
        initProofStarter(po);
    }

    private void simplifyUpdate() {                        
        this.setUpProof(DefaultImmutableSet.<Term>nil().add(TB.not(programPio.constrainedFormula().formula())), 
                null);
        
        vd.setInitPhase(true);
        vd.getBpManager().setNoEx(true);

        final ProofEnvironment env = mediator.getProof().env();

        final Proof simplificationProof = ps.getProof();
        
        StrategyProperties strategyProperties = DebuggerStrategy
                .getDebuggerStrategyProperties(true, true, vd.isInitPhase(),new LinkedList<WatchPoint>());

        StrategyFactory factory = new DebuggerStrategy.Factory();
        
        mediator.getProof().
        setActiveStrategy(factory.create(mediator.getProof(), strategyProperties));
        
        ps.run(env);
        
        vd.setInitPhase(false);
        vd.getBpManager().setNoEx(false);

        strategyProperties = 
            DebuggerStrategy.getDebuggerStrategyProperties(true, false, vd.isInitPhase(),new LinkedList<WatchPoint>());
        
        mediator.getProof().
        setActiveStrategy(factory.create(mediator.getProof(), strategyProperties));

       

        assert simplificationProof.openGoals().size() == 1;
        
        final Goal openGoal = simplificationProof.openGoals().head();
        this.programPio = vd.getProgramPIO(openGoal.sequent());
        if (programPio == null) {
            programPio = vd.getExecutionTerminatedNormal(openGoal.node());
        }
    }

}
