package de.uka.ilkd.key.visualdebugger.statevisualisation;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ListOfSort;
import de.uka.ilkd.key.logic.sort.SLListOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.updatesimplifier.*;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.DebuggerPO;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;

public class StateVisualization {

    private SetOfTerm arrayIndexTerms;

    private final SetOfTerm arrayLocations;

    private SetOfTerm[][] indexConfigurations;

    private SetOfTerm[] instanceConfigurations;

    private final ITNode itNode;

    private final ListOfTerm locations;

    private final KeYMediator mediator;

    // ListOfTerm terms = SLListOfTerm.EMPTY_LIST;

    private DebuggerPO po = new DebuggerPO("DebuggerPo");

    private Term[] postAttributes;

    private ListOfTerm[][] postValues;

    private PosInOccurrence programPio;

    private Term programPio2;

    private ProofStarter ps;

    private SetOfTerm refInPC = SetAsListOfTerm.EMPTY_SET;

    private final Services serv;

    private RigidFunction stateOp;

    private Term statePred;

    private VisualDebugger vd = VisualDebugger.getVisualDebugger();

    public StateVisualization(ITNode itn, KeYMediator mediator) {
        this.itNode = itn;

        this.mediator = mediator;

        this.serv = mediator.getServices();

        refInPC = getReferences(itNode.getPc());
        VisualDebugger.print("References in PC: ");
        VisualDebugger.print(refInPC);

        this.programPio = VisualDebugger.getVisualDebugger().getProgramPIO(
                itNode.getNode().sequent());
        if (programPio == null) {
            programPio = VisualDebugger.getVisualDebugger()
                    .getExecutionTerminatedNormal(itNode.getNode());
        }
        if (programPio == null)
            throw new RuntimeException("Program Pio not found in Sequent "
                    + itNode.getNode().sequent());
        // System.out.println("Program Pio "+programPio);
        simplifyUpdate();
        // System.out.println("Simpified Program PIo "+programPio);
        setUpProof();

        locations = vd.getLocations(programPio);
        arrayIndexTerms = vd.getArrayIndex(programPio);

        // getRefsInPreState(locations);
        arrayLocations = vd.getArrayLocations(programPio);
        VisualDebugger.print("Locations " + locations);
        // System.out.println("Refs in Locations "+this.changedObjects);
        // System.out.println("AttributeOps "+this.changedAttributes);
        VisualDebugger.print("Array Index Terms " + this.arrayIndexTerms);

        VisualDebugger.print("Formual"
                + programPio.constrainedFormula().formula());

        programPio2 = addRememberPrestateUpdates(programPio
                .constrainedFormula().formula());
        // statePred = this.createPredicate(locations);

        VisualDebugger.print("Add Rememberpres " + programPio2);
        // IteratorOfTerm it1 = this.nonPrimTerms.iterator();
        // IteratorOfTerm it2 = this.nonPrimTerms.iterator();

        applyCuts(refInPC);

        VisualDebugger
                .print("----------- Open Goals after ref case distinctions -------");
        VisualDebugger.print(ps.getProof().openGoals());

        computeInstanceConfigurations();
        this.indexConfigurations = new SetOfTerm[this.instanceConfigurations.length][];
        for (int i = 0; i < instanceConfigurations.length; i++) {
            setUpProof(instanceConfigurations[i]);
            applyCuts(arrayIndexTerms);
            VisualDebugger
                    .print("----------- Open Goals after array case dist ---------");
            VisualDebugger.print("InstanceConf " + instanceConfigurations[i]);
            VisualDebugger.print(ps.getProof().openGoals());
            computeArrayConfigurations(i);
        }

        postValues = new ListOfTerm[instanceConfigurations.length][];
        for (int i = 0; i < instanceConfigurations.length; i++) {
            postValues[i] = new ListOfTerm[indexConfigurations[i].length];
            for (int j = 0; j < indexConfigurations[i].length; j++) {
                this.setUpProofForPostValues(instanceConfigurations[i]
                        .union(indexConfigurations[i][j]));
                VisualDebugger.print("Determining Post Values");
                vd.setDeterminePostValue(true);
                ps.run(mediator.getProof().env());
                vd.setDeterminePostValue(false);
                postValues[i][j] = getPostState(ps.getProof().openGoals()
                        .iterator().next().node().sequent());
                VisualDebugger.print("Open goals after res Updates");
                VisualDebugger.print(ps.getProof().openGoals());
            }
        }

        // for(IteratorOfGoal it =
        // ps.getProof().openGoals().iterator();it.hasNext();)
        // applyCutsForPost(it.next());
        // getPostStates(ps.getProof().openGoals());
        VisualDebugger.getVisualDebugger().fireDebuggerEvent(
                new DebuggerEvent(DebuggerEvent.VIS_STATE, this));
    }

    private Term addRememberPrestateUpdates(Term target) {
        // QuanUpdateOperator op =
        // QuanUpdateOperator.createUpdateOp(this.refsInPreState.toArray(), new
        // boolean[locations.size()]);
        Term locs[] = locations.toArray();
        postAttributes = new Term[locs.length];

        Update up = Update.createUpdate(target);

        LinkedList newAP = new LinkedList();
        // for(IteratorOfTerm it= this.refsInPreState.iterator();it.hasNext();){
        for (int i = 0; i < locs.length; i++) {
            if (locs[i].op() instanceof AttributeOp) {
                final LocationVariable pv = new LocationVariable(
                        new ProgramElementName("pre" + i), locs[i].sub(0)
                                .sort());
                final Term t = TermFactory.DEFAULT.createFunctionTerm(pv);
                postAttributes[i] = TermFactory.DEFAULT.createAttributeTerm(
                        AttributeOp.getAttributeOp(((AttributeOp) locs[i].op())
                                .attribute()), t);

                newAP.add(new AssignmentPairImpl(pv, new Term[0], locs[i]
                        .sub(0)));
                // System.out.println("APS "+aps[i]);
            } else if (locs[i].op() instanceof ProgramVariable) {
                postAttributes[i] = locs[i];

            } else if (locs[i].op() instanceof ArrayOp) {
                final LocationVariable pv_array_ref = new LocationVariable(
                        new ProgramElementName("pre_array_" + i), locs[i]
                                .sub(0).sort());
                final Term t = TermFactory.DEFAULT
                        .createFunctionTerm(pv_array_ref);

                newAP.add(new AssignmentPairImpl(pv_array_ref, new Term[0],
                        locs[i].sub(0)));

                final LocationVariable pv_index = new LocationVariable(
                        new ProgramElementName("pre_array_index_" + i), locs[i]
                                .sub(1).sort());

                final Term indexT = TermFactory.DEFAULT
                        .createFunctionTerm(pv_index);
                newAP.add(new AssignmentPairImpl(pv_index, new Term[0], locs[i]
                        .sub(1)));

                postAttributes[i] = TermFactory.DEFAULT.createArrayTerm(
                        (ArrayOp) locs[i].op(), t, indexT);

                // aps[i]= new AssignmentPairImpl(pv_array_ref, new Term[0],
                // locs[i].sub(0));

            }

        }

        ArrayOfAssignmentPair apOld = up.getAllAssignmentPairs();
        AssignmentPair[] aps = new AssignmentPair[newAP.size() + apOld.size()];

        // System.out.println(apOld.size()+" "+newAP.size());
        for (int i = newAP.size(); i < apOld.size() + newAP.size(); i++) {
            // System.out.println(i);

            aps[i] = apOld.getAssignmentPair(i - newAP.size());

        }

        for (int i = 0; i < newAP.size(); i++) {
            aps[i] = (AssignmentPair) newAP.get(i); // TODO

        }

        statePred = createPredicate(SLListOfTerm.EMPTY_LIST
                .append(postAttributes));

        return UpdateSimplifierTermFactory.DEFAULT.createUpdateTerm(aps,
                this.statePred);

    }

    private synchronized void applyCutAndRun(ListOfGoal goals, Term inst) {
        for (IteratorOfGoal it = goals.iterator(); it.hasNext();) {
            Goal g = it.next();
            NoPosTacletApp c = g.indexOfTaclets().lookup("cut");
            assert (c != null);
            // c.
            SetOfSchemaVariable set2 = c.neededUninstantiatedVars();
            SchemaVariable cutF = set2.iterator().next();

            TacletApp t2 = c.addInstantiation(cutF, inst, false);

            g.apply(t2);

            ps.run(mediator.getProof().env());
        }

    }

    private HashMap applyCuts(SetOfTerm terms) {
        HashMap goal2cutFormulas = new HashMap();
        Term[] t1 = terms.toArray();
        Term[] t2 = terms.toArray();

        for (int i1 = 0; i1 < t1.length; i1++) {
            for (int i2 = i1; i2 < t2.length; i2++) {
                // System.out.println("adsf");
                if (!t1[i1].equals(t2[i2])) {
                    // terms = terms.append(this.createEqu(t1[i1], t2[i2]));
                    if (t1[i1].sort().extendsTrans(t2[i2].sort())
                            || t2[i2].sort().extendsTrans(t1[i1].sort())) {
                        // System.out.println("Cut and run to all open goals
                        // "+createEqu(t1[i1], t2[i2]));
                        applyCutAndRun((ps.getProof().openGoals()), createEqu(
                                t1[i1], t2[i2]));
                    }
                }
            }
        }
        return goal2cutFormulas;

    }

    private void computeArrayConfigurations(int instanceConf) {
        HashSet indexConf = new HashSet();
        for (IteratorOfGoal it = ps.getProof().openGoals().iterator(); it
                .hasNext();) {
            indexConf.add(getAppliedCutsSet(it.next().node(), ps.getProof()
                    .root()));
        }
        this.indexConfigurations[instanceConf] = new SetOfTerm[indexConf.size()];
        int i = 0;
        for (Iterator it = indexConf.iterator(); it.hasNext();) {
            Object c = it.next();
            indexConfigurations[instanceConf][i] = (SetOfTerm) c;
            // System.out.println("ArrayConf "+c);
            i++;
        }

    }

    private void computeInstanceConfigurations() {
        HashSet indexConf = new HashSet();
        for (IteratorOfGoal it = ps.getProof().openGoals().iterator(); it
                .hasNext();) {
            indexConf.add(getAppliedCutsSet(it.next().node(), ps.getProof()
                    .root()));
        }
        this.instanceConfigurations = new SetOfTerm[indexConf.size()];
        int i = 0;
        for (Iterator it = indexConf.iterator(); it.hasNext();) {
            Object c = it.next();
            instanceConfigurations[i] = (SetOfTerm) c;
            // System.out.println("IndexConf "+c);
            i++;
        }

    }

    private Term createEqu(Term t1, Term t2) {
        return TermFactory.DEFAULT.createEqualityTerm(t1, t2);
    }

    private Term createPredicate(ListOfTerm locs) {
        Term result = null;
        // Sort sorts[]=new Sort[locs.size()];
        ListOfSort s = SLListOfSort.EMPTY_LIST;

        for (IteratorOfTerm it = locs.iterator(); it.hasNext();) {
            s = s.append(it.next().sort());
        }

        stateOp = new RigidFunction(new Name("STATE"), Sort.FORMULA, s
                .toArray());

        result = TermFactory.DEFAULT
                .createFunctionTerm(stateOp, locs.toArray());

        return result;
    }

    private SetOfTerm getAppliedCutsSet(Node n, Node root) {
        // System.out.println("getAppliedCuts "+n.serialNr()+"
        // "+root.serialNr());
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        if (!root.find(n)) {
            // System.out.println(n.serialNr()+" "+root.serialNr());
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
                        inst = TermFactory.DEFAULT.createJunctorTerm(Op.NOT,
                                inst);
                    result = result.add(inst);

                }
            }
        }

        return result;

    }

    public SetOfTerm[] getPossibleIndexTermsForPcState(int i) {
        return indexConfigurations[i];

    }

    private ListOfTerm getPostState(Sequent s) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        for (IteratorOfConstrainedFormula it = s.succedent().iterator(); it
                .hasNext();) {
            ConstrainedFormula cfm = it.next();
            if (cfm.formula().op() == stateOp) {
                for (int i = 0; i < cfm.formula().arity(); i++) {
                    result = result.append(cfm.formula().sub(i));
                }

            }

        }
        return result;
    }

    private SetOfTerm getReferences(ListOfTerm terms) {
        // ListOfTerm pc = itNode.getPc();
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        for (IteratorOfTerm it = terms.iterator(); it.hasNext();) {
            result = result.union(getReferences(it.next()));
        }
        return result;
    }

    private SetOfTerm getReferences(Term t) {
        // System.out.println(t);
        // if (t.sort()!= Sort.FORMULA && !this.isBool(t)&&!this.isInt(t))

        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        if (referenceSort(t.sort()) && t.freeVars().size() == 0)
            result = result.add(t);
        for (int i = 0; i < t.arity(); i++) {
            result = result.union(getReferences(t.sub(i)));
        }
        return result;
    }

    public SymbolicObjectDiagram getSymbolicState(int i, SetOfTerm indexTerms,
            boolean pre) {
        for (int j = 0; j < indexConfigurations[i].length; j++) {
            if (indexTerms.subset(indexConfigurations[i][j])) {
                VisualDebugger.print("Found " + j);
                final ListOfTerm pt = postValues[i][j];
                SymbolicObjectDiagram s = new SymbolicObjectDiagram(itNode,
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
        JavaInfo info = serv.getJavaInfo();
        KeYJavaType kjt = info.getKeYJavaType(s);
        // System.out.println(kjt);
        if (kjt == null)
            return false;
        if (kjt.getJavaType() instanceof ClassType
                || kjt.getJavaType() instanceof ArrayDeclaration) // TODO ??
            return true;

        return false;
    }

    private void setUpProof() {
        po = new DebuggerPO("DebuggerPo");
        ps = new ProofStarter();
        po.setUp(vd.getPrecondition(), itNode);
        po.setIndices(mediator.getProof().env().getInitConfig()
                .createTacletIndex(), mediator.getProof().env().getInitConfig()
                .createBuiltInRuleIndex());
        po.setProofSettings(mediator.getProof().getSettings());
        po.setConfig(mediator.getProof().env().getInitConfig());
        ps.init(po);
        vd.setProofStrategy(ps.getProof(), true, false);
    }

    private void setUpProof(SetOfTerm indexConf) {
        po = new DebuggerPO("DebuggerPo");
        ps = new ProofStarter();
        po.setUp(vd.getPrecondition(), itNode, indexConf);
        po.setIndices(mediator.getProof().env().getInitConfig()
                .createTacletIndex(), mediator.getProof().env().getInitConfig()
                .createBuiltInRuleIndex());
        po.setProofSettings(mediator.getProof().getSettings());
        po.setConfig(mediator.getProof().env().getInitConfig());
        ps.init(po);
        vd.setProofStrategy(ps.getProof(), true, false);
    }

    private void setUpProofForPostValues(SetOfTerm indexConf) {
        po = new DebuggerPO("DebuggerPo");
        ps = new ProofStarter();
        po.setUp(vd.getPrecondition(), itNode, indexConf, programPio2);
        po.setIndices(mediator.getProof().env().getInitConfig()
                .createTacletIndex(), mediator.getProof().env().getInitConfig()
                .createBuiltInRuleIndex());
        po.setProofSettings(mediator.getProof().getSettings());
        po.setConfig(mediator.getProof().env().getInitConfig());
        ps.init(po);
        vd.setProofStrategy(ps.getProof(), true, false);
    }

    private void simplifyUpdate() {
        this.setUpProof(SetAsListOfTerm.EMPTY_SET.add(TermFactory.DEFAULT
                .createJunctorTerm(Op.NOT, programPio.constrainedFormula()
                        .formula())));

        VisualDebugger.getVisualDebugger().setInitPhase(true);
        VisualDebugger.getVisualDebugger().getBpManager().setNoEx(true);

        final Proof proof = mediator.getProof();

        StrategyProperties strategyProperties = DebuggerStrategy
                .getDebuggerStrategyProperties(true, true, VisualDebugger
                        .getVisualDebugger().isInitPhase());

        StrategyFactory factory = new DebuggerStrategy.Factory();
        proof.setActiveStrategy(factory.create(proof, strategyProperties));

        ps.run(proof.env());

        VisualDebugger.getVisualDebugger().setInitPhase(false);
        VisualDebugger.getVisualDebugger().getBpManager().setNoEx(false);

        strategyProperties = DebuggerStrategy.getDebuggerStrategyProperties(
                true, false, VisualDebugger.getVisualDebugger().isInitPhase());

        proof.setActiveStrategy(factory.create(proof, strategyProperties));

        // System.out.println(ps.getProof().openGoals().iterator().next().sequent());
        this.programPio = VisualDebugger.getVisualDebugger().getProgramPIO(
                ps.getProof().openGoals().iterator().next().sequent());
        if (programPio == null) {
            programPio = VisualDebugger.getVisualDebugger()
                    .getExecutionTerminatedNormal(
                            ps.getProof().openGoals().iterator().next().node());
        }
    }

}
