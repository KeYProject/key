// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.statevisualisation;

import java.util.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayOfParameterDeclaration;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.visualdebugger.Label;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;

public class SymbolicObjectDiagram {
    private static Term nullTerm = TermFactory.DEFAULT
            .createFunctionTerm(Op.NULL);

    public static boolean checkIndices(Term t, Services serv) {
        if (t.op() instanceof AttributeOp) {
            return checkIndices(t.sub(0), serv);
        }
        if (t.op() instanceof ArrayOp) {
            if (serv.getTypeConverter().getIntegerLDT().getNumberSymbol() == t.sub(1).op()) {
                if (AbstractMetaOperator.convertToDecimalString(t.sub(1), serv)
                        .startsWith("-")) {
                    return false;
                }
            }
            return checkIndices(t.sub(0), serv);
        }
        return true;
    }

    public static boolean isLocation(Term t, Services serv) {
        OpCollector oc = new OpCollector();
        t.execPostOrder(oc);
        if (oc.contains(Op.NULL)) {
            return false;
        }
        
        final IntegerLDT iLDT = serv.getTypeConverter().getIntegerLDT();
        final BooleanLDT bLDT = serv.getTypeConverter().getBooleanLDT();
        
        final Function numberTerminator = iLDT.getNumberTerminator();
        final Function boolTRUE = bLDT.getTrueConst();
        final Function boolFALSE = bLDT.getFalseConst();
        
        
        final Operator op = t.op();
        return op instanceof AttributeOp
                && checkIndices(t, serv)
                && !((ProgramVariable) ((AttributeOp) op).attribute()).isImplicit() 
                || op instanceof ProgramVariable
                && !((ProgramVariable) op).isImplicit()
                || op instanceof ArrayOp && checkIndices(t, serv)
                // TODO Why is a RigidFunction a location? 
                // Was a ProgramConstant intended? if so replace the rest
                // by instanceof ProgramConstant
                || op instanceof RigidFunction && t.arity() == 0
                && numberTerminator != op
                && boolTRUE != op
                && boolFALSE != op
                // TODO remove string comparison in next line
                && op.name().toString().indexOf("undef(") == -1;
    }

    private ListOfTerm ante = SLListOfTerm.EMPTY_LIST;
            
    private ListOfTerm succ = SLListOfTerm.EMPTY_LIST;

    private SetOfTerm arrayLocations;

    private SetOfTerm indexTerms;

    private SetOfTerm instanceConfiguration;

    private ITNode itNode;

    private SetOfTerm locations = SetAsListOfTerm.EMPTY_SET;

    private Term methodReferences[];

    private Node node;

    ListOfTerm pc = SLListOfTerm.EMPTY_LIST;

    private SetOfTerm[] possibleIndexTerms;

    private ListOfTerm postTerms;

    private HashMap<Term, Integer> ref2ser;

    private SetOfTerm refInPC = SetAsListOfTerm.EMPTY_SET;

    private Services serv;

    private LinkedList<SymbolicObject> symbolicObjects;

    private HashMap<Term, EquClass> term2class;

    LinkedList terms = new LinkedList();

    private VisualDebugger vd;

    public SymbolicObjectDiagram(ITNode itNode, Services serv, ListOfTerm pc,
            SetOfTerm refInPC, ListOfTerm preTerms, ListOfTerm postTerms,
            boolean pre, SetOfTerm arrayLocations,
            SetOfTerm[] possibleIndexTerms, SetOfTerm indexTerms,
            SetOfTerm instanceConfiguration) {
        this.instanceConfiguration = instanceConfiguration;

        prepare(itNode, serv, pc, refInPC);

        this.postTerms = postTerms;

        this.arrayLocations = arrayLocations;

        this.possibleIndexTerms = possibleIndexTerms;

        this.indexTerms = indexTerms;

        createSymbolicObjects();

        if (!pre) {
            createSymbolicObjectsForNewInstances(preTerms);
            createPostState(preTerms, postTerms);
            setMethodStack(pre);
        }

        setInstanceNames(symbolicObjects);
    }

    private void addArrayEntry(LinkedList<SymbolicObject> objects, Term ref, Term index,
            Term con) {
        final Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            if (so.getTerms().contains(ref)) {
                ((SymbolicArrayObject) so).addIndexConstraint(index, con);
            }
        }

    }

    private void addAttribute(LinkedList<SymbolicObject> objects, AttributeOp op, Term sub,
            Term cTerm) {
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            if (so.getTerms().contains(sub)) {
                if (!((ProgramVariable) op.attribute()).isImplicit()
                        || VisualDebugger.showImpliciteAttr)
                    so.addAttributeConstraint((ProgramVariable) op.attribute(),
                            cTerm);
            }
        }

    }

    private void addIndexReference(Term sub, Term index,
            SymbolicObject soReferenced, LinkedList<SymbolicObject> objects) {
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            if (so.getTerms().contains(sub)) {
                ((SymbolicArrayObject) so).addAssociationFromIndex(index,
                        soReferenced);
            }
        }
    }

    private void addReference(AttributeOp op, Term sub,
            SymbolicObject soReferenced, LinkedList<SymbolicObject> objects) {
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            if (so.getTerms().contains(sub)) {
                if (op.attribute() instanceof ProgramVariable)
                    so.addAssociation(op.attribute(), soReferenced);
                else
                    System.err
                            .println("op.attribute not instance of ProgramVariable");
            }
        }
    }

    private void addStaticAttribute(LinkedList<SymbolicObject> objects, ProgramVariable pv,
            ClassType ct, Term cTerm) {
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            if (so.isStatic() && so.getType().equals(ct)) {
                if (!pv.isImplicit() || VisualDebugger.showImpliciteAttr)
                    so.addAttributeConstraint(pv, cTerm);
            }
        }

    }

    private void addStaticReference(ProgramVariable op,
            SymbolicObject soReferenced, LinkedList<SymbolicObject> objects) {
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            if (so.isStatic() 
                    && so.getType().equals(op.getContainerType().getJavaType()))
                so.addAssociation(op, soReferenced);

        }

    }

    private void collectLocations(Term t) {
        if (isLocation(t, serv)) {
            getEqvClass(t);
            locations = locations.add(t);
        }
        if (!(t.op() instanceof Modality || t.op() instanceof IUpdateOperator || t
                .op() instanceof Quantifier)) {
            for (int i = 0; i < t.arity(); i++) {
                collectLocations(t.sub(i));
            }
        }
    }

    private SetOfTerm collectLocations2(Term t) {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        if (isLocation(t, serv)) {
            result = result.add(t);

        }
        if (!(t.op() instanceof Modality || t.op() instanceof IUpdateOperator || t
                .op() instanceof Quantifier)) {
            for (int i = 0; i < t.arity(); i++) {
                result = result.union(collectLocations2(t.sub(i)));
            }
        }
        return result;
    }

    private boolean containsJavaBlock(Term t) {
        if (t.op() == vd.getPostPredicate()) {
            return true; // TODO
        }
        if (!t.javaBlock().isEmpty()) {
            return true;
        }
        for (int i = 0; i < t.arity(); i++) {
            if (containsJavaBlock(t.sub(i))) {
                return true;
            }
        }
        return false;
    }

    private void createEquivalenceClassesAndConstraints() {
        term2class = new HashMap<Term, EquClass>();
        IteratorOfTerm it = ante.iterator();
        while (it.hasNext()) {
            EquClass ec = null;
            Term t = it.next();
            collectLocations(t);
            if (t.op() instanceof Equality /* && !containsImplicitAttr(t) */) {
                if (term2class.containsKey(t.sub(0))) {
                    ec = term2class.get(t.sub(0));
                    if (term2class.containsKey(t.sub(1))) {
                        ec.add(term2class.get(t.sub(1)));
                    } else {
                        ec.add(t.sub(1));
                    }
                } else if (term2class.containsKey(t.sub(1))) {
                    ec = term2class.get(t.sub(1));
                    ec.add(t.sub(0));
                } else {
                    ec = new EquClass(t.sub(0), t.sub(1));
                }
                IteratorOfTerm ecIt = ec.getMembers().iterator();
                while (ecIt.hasNext()) {
                    term2class.put(ecIt.next(), ec);
                }
            }

        }
        it = succ.iterator();
        while (it.hasNext()) {
            Term t = it.next();
            collectLocations(t);
        }
    }

    private void createPostState(ListOfTerm pre, ListOfTerm post) {
        VisualDebugger.print("createPostState -----");
        IteratorOfTerm pIt = post.iterator();
        for (IteratorOfTerm it = pre.iterator(); it.hasNext();) {
            Term preTerm = it.next();
            Term postTerm = pIt.next();
            // System.out.println(preTerm+":="+postTerm);
            if (preTerm.op() instanceof AttributeOp) {
                final Term sub = preTerm.sub(0);
                final SymbolicObject so = getObject(sub, symbolicObjects);
                if (referenceSort(preTerm.sort()))
                    so.addAssociation(((AttributeOp) preTerm.op()).attribute(),
                            getObject(postTerm, symbolicObjects));
                else if (!((ProgramVariable) ((AttributeOp) preTerm.op())
                        .attribute()).isImplicit()
                        || VisualDebugger.showImpliciteAttr)
                    so.addValueTerm((ProgramVariable) ((AttributeOp) preTerm
                            .op()).attribute(), postTerm);
            } else if (preTerm.op() instanceof ArrayOp) {
                final Term sub = preTerm.sub(0);
                final SymbolicArrayObject sao = (SymbolicArrayObject) getObject(
                        sub, symbolicObjects);
                if (referenceSort(preTerm.sort()))
                    sao.addAssociationFromIndex(preTerm.sub(1), getObject(
                            postTerm, symbolicObjects));
                else
                    sao.setValueTermForIndex(preTerm.sub(1), postTerm);
            } else if (preTerm.op() instanceof ProgramVariable) {
                final ProgramVariable pv = (ProgramVariable) preTerm.op();
                SymbolicObject staticO = getStaticObject((ClassType) pv
                        .getContainerType().getJavaType(), symbolicObjects);
                if (staticO == null) {
                    if (!pv.isImplicit() || VisualDebugger.showImpliciteAttr) {
                        staticO = new SymbolicObject((ClassType) pv
                                .getContainerType().getJavaType(), serv);
                        symbolicObjects.add(staticO);
                    }
                }

                if (referenceSort(preTerm.sort()))
                    staticO.addAssociation(pv, getObject(postTerm,
                            symbolicObjects));
                else if (!pv.isImplicit() || VisualDebugger.showImpliciteAttr)
                    staticO.addValueTerm(pv, postTerm);
            }

        }

    }

    private void createSymbolicObjects() {
        LinkedList<SymbolicObject> result = new LinkedList<SymbolicObject>();
        EquClass[] npClasses = getNonPrimitiveLocationEqvClasses();
        for (int i = 0; i < npClasses.length; i++) {
            KeYJavaType t = npClasses[i].getKeYJavaType();
            if (!disjunct(npClasses[i].getMembers(), refInPC)) {
                if (npClasses[i].isArray()) {
                    SymbolicArrayObject sao = new SymbolicArrayObject(
                            npClasses[i].getMembers(), (ClassType) t
                                    .getJavaType(), serv);
                    sao
                            .setPossibleIndexTermConfigurations(getPossibleIndexTerms(npClasses[i]
                                    .getMembers()));
                    sao.setIndexConfiguration(getPossibleIndexTermsForArray(sao
                            .getTerms(), indexTerms));
                    result.add(sao);
                } else
                    result.add(new SymbolicObject(npClasses[i].getMembers(),
                            (ClassType) t.getJavaType(), serv));

            }
        }

        // create static objects
        // System.out.println("Static Type "+);
        for (Iterator<Type> it = this.getStaticClasses().iterator(); it.hasNext();) {
            result.add(new SymbolicObject((ClassType) (it.next()), serv));
        }

        // create self object/ self static class, if not happened
        if (vd.isStaticMethod()) {
            final ClassType ct = vd.getType();
            if (this.getStaticObject(ct, result) == null)
                result.add(new SymbolicObject(ct, serv));
        } else {
            final Term self = (Term) vd.getInputPV2term().get(
                    (vd.getSelfTerm()));
            if (this.getObject(self, result) == null)
                result.add(new SymbolicObject(self, (ClassType) serv
                        .getJavaInfo().getKeYJavaType(self.sort())
                        .getJavaType(), serv));
        }

        // create unknown objects
        for (IteratorOfTerm it = postTerms.iterator(); it.hasNext();) {
            Term next = it.next();
            if (this.referenceSort(next.sort())
                    && !VisualDebugger.containsImplicitAttr(next)) {
                if (getObject(next, result) == null) {
                    result.add(new SymbolicObject(next, (ClassType) serv
                            .getJavaInfo().getKeYJavaType(next.sort())
                            .getJavaType(), serv, true));
                }

            }

        }

        // Compute Associations...
        Iterator<SymbolicObject> it = result.iterator();
        while (it.hasNext()) {
            SymbolicObject so = it.next();
            IteratorOfTerm it2 = so.getTerms().iterator();
            // SetOfTerm result;
            // System.out.println("adding assos");
            while (it2.hasNext()) {

                Term t = it2.next();
                // System.out.println("ref" +t);

                if (t.op() instanceof AttributeOp) {
                    Term sub = t.sub(0);
                    AttributeOp op = (AttributeOp) t.op();                
                    if (refInPC.contains(t) || postTerms.contains(t)) // TODO
                                                                        // ???//only
                                                                        // assoc
                                                                        // that
                                                                        // are
                                                                        // in
                                                                        // the
                                                                        // pc
                        addReference(op, sub, so, result);
                } else if (t.op() instanceof ArrayOp) {
                    if (refInPC.contains(t) || postTerms.contains(t)) // TODO??
                        addIndexReference(t.sub(0), t.sub(1), so, result);

                } else if (t.op() instanceof ProgramVariable && 
                        ((ProgramVariable)t.op()).isMember()) {
                    if (refInPC.contains(t) || postTerms.contains(t)) // TODO
                                                                        // ???//only
                                                                        // assoc
                                                                        // that
                                                                        // are
                                                                        // in
                                                                        // the
                                                                        // pc
                        addStaticReference((ProgramVariable) t.op(), so, result);

                }

            }
        }

        for (IteratorOfTerm it2 = pc.iterator(); it2.hasNext();) {
            Term currentTerm = it2.next();
            SetOfTerm locs = collectLocations2(currentTerm);

            for (IteratorOfTerm it3 = locs.iterator(); it3.hasNext();) {

                Term t2 = it3.next();
                if (!referenceSort(t2.sort())) {
                    if (t2.op() instanceof AttributeOp) {
                        addAttribute(result, (AttributeOp) t2.op(), t2.sub(0),
                                currentTerm);
                    } else if (t2.op() instanceof ArrayOp) {
                        this.addArrayEntry(result, t2.sub(0), t2.sub(1),
                                currentTerm);
                    } else if (t2.op() instanceof ProgramVariable) {
                        ProgramVariable pv = (ProgramVariable) t2.op();
                        KeYJavaType kjt = pv.getContainerType();
                        if (kjt != null) {
                            ClassType ct = (ClassType) kjt.getJavaType();
                            this
                                    .addStaticAttribute(result, pv, ct,
                                            currentTerm);

                        }

                    }

                }

            }
        }
        setInstanceNames(result);
        symbolicObjects = result;
    }

    private void createSymbolicObjectsForNewInstances(ListOfTerm pre) {
        for (IteratorOfTerm it = pre.iterator(); it.hasNext();) {
            Term next = it.next();

            if (next.op() instanceof AttributeOp) {
                Term sub = next.sub(0);

                if (getObject(sub, this.symbolicObjects) == null) {
                    symbolicObjects.add(new SymbolicObject(sub,
                            (ClassType) serv.getJavaInfo().getKeYJavaType(
                                    sub.sort()).getJavaType(), this.serv));
                }

            }
        }

    }

    private boolean disjunct(SetOfTerm s1, SetOfTerm s2) {
        for (IteratorOfTerm it = s1.iterator(); it.hasNext();) {
            if (s2.contains(it.next()))
                return false;
        }
        return true;
    }

    private LinkedList<SymbolicObject> filterStaticObjects(LinkedList<SymbolicObject> objects) {
        LinkedList<SymbolicObject> result = new LinkedList<SymbolicObject>();
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            final SymbolicObject so = it.next();
            if (!so.isStatic())
                result.add(so);
        }
        return result;
    }

    private void findDisjointClasses() {
        IteratorOfTerm it = succ.iterator();
        while (it.hasNext()) {
            Term t = it.next();
            EquClass e0, e1;
            if (t.op() instanceof Equality /* &&!containsImplicitAttr(t) */) {
                e0 = getEqvClass(t.sub(0));
                e1 = getEqvClass(t.sub(1));
                e0.addDisjoint(t.sub(1));
                e1.addDisjoint(t.sub(0));
            }
        }
    }

    public ListOfTerm getConstraints(Term toFind) {
        // Term pvTerm = TermFactory.DEFAULT.createVariableTerm(pv);
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        for (IteratorOfTerm it = pc.iterator(); it.hasNext();) {
            final Term t = it.next();
            OpCollector vis = new OpCollector();
            t.execPostOrder(vis);

            if (vis.contains(toFind.op()))
                result = result.append(t);

            // System.out.println(vis.);

        }

        return result;

    }

    private EquClass getEqvClass(Term t) {
        if (!term2class.containsKey(t)) {
            term2class.put(t, new EquClass(t));
        }
        return term2class.get(t);
    }

    public SetOfTerm getIndexTerms() {
        return indexTerms;
    }

    public EquClass[] getNonPrimitiveLocationEqvClasses() {
        Object[] oa = (new HashSet<EquClass>(term2class.values())).toArray();
        EquClass[] temp = new EquClass[oa.length];
        int l = 0;
        for (int i = 0; i < oa.length; i++) {
            if (((EquClass) oa[i]).getLocations().size() > 0
                    && (!((EquClass) oa[i]).isInt() && !((EquClass) oa[i])
                            .isBoolean())) {
                temp[l++] = (EquClass) oa[i];
            }
        }
        EquClass[] result = new EquClass[l];
        for (int i = 0; i < l; i++) {
            result[i] = temp[i];
        }
        return result;
    }

    private SymbolicObject getObject(Term sub, LinkedList<SymbolicObject> objects) {
        Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            final SymbolicObject so = it.next();
            if (so.getTerms().contains(sub)) {
                return so;
            }
        }
        return null;
    }

    private ListOfTerm getPc(HashMap<PosInOccurrence, Label> labels) {
        ListOfTerm pc2 = SLListOfTerm.EMPTY_LIST;

        for (final PosInOccurrence pio : labels.keySet()) {
            // PCLabel pcLabel = ((PCLabel)labels.get(pio));
            if (!containsJavaBlock(pio.constrainedFormula().formula())) {
                Term t = pio.constrainedFormula().formula();
                if (pio.isInAntec())
                    pc2 = pc2.append(t);
                else {
                    if (t.op() == Op.NOT) {
                        pc2 = pc2.append(t.sub(0));
                    } else
                        pc2 = pc2.append(TermFactory.DEFAULT
                                .createJunctorTermAndSimplify(Op.NOT, t));
                }

                // pc = pc.append(pio.constrainedFormula().formula());
            }

        }
        return pc2;
    }

    private LinkedList<SetOfTerm> getPossibleIndexTerms(SetOfTerm members) {
        LinkedList<SetOfTerm> result = new LinkedList<SetOfTerm>();
        if (possibleIndexTerms != null)
            for (int i = 0; i < possibleIndexTerms.length; i++) {
                SetOfTerm currentIndexTerms = possibleIndexTerms[i];
                SetOfTerm locInd = SetAsListOfTerm.EMPTY_SET;
                SetOfTerm res = SetAsListOfTerm.EMPTY_SET;

                for (IteratorOfTerm locIt = this.arrayLocations.iterator(); locIt
                        .hasNext();) {
                    Term t = locIt.next();
                    if (members.contains(t.sub(0))) {
                        locInd = locInd.add(t.sub(1));
                    }
                }

                for (IteratorOfTerm posIndexTermsIt = currentIndexTerms
                        .iterator(); posIndexTermsIt.hasNext();) {
                    final Term t = posIndexTermsIt.next();
                    final Term t2;
                    if (t.op() == Op.NOT)
                        t2 = t.sub(0);
                    else
                        t2 = t;
                    if (locInd.contains(t2.sub(0))
                            && locInd.contains(t2.sub(1)))
                        res = res.add(t);
                }
                result.add(res);
            }
        // VisualDebugger.print("POS INDEX TERMS "+result);
        return result;

    }

    private SetOfTerm getPossibleIndexTermsForArray(SetOfTerm members,
            SetOfTerm ic) {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;

        SetOfTerm currentIndexTerms = ic;
        SetOfTerm locInd = SetAsListOfTerm.EMPTY_SET;
        for (IteratorOfTerm locIt = this.arrayLocations.iterator(); locIt
                .hasNext();) {
            Term t = locIt.next();
            if (members.contains(t.sub(0))) {
                locInd = locInd.add(t.sub(1));
            }
        }

        for (IteratorOfTerm posIndexTermsIt = currentIndexTerms.iterator(); posIndexTermsIt
                .hasNext();) {
            final Term t = posIndexTermsIt.next();
            final Term t2;
            if (t.op() == Op.NOT)
                t2 = t.sub(0);
            else
                t2 = t;
            if (locInd.contains(t2.sub(0)) && locInd.contains(t2.sub(1)))
                result = result.add(t);
        }
        // result=(res);

        // VisualDebugger.print("Index terms for member"+ members+" :"+result);
        return result;

    }

    // TODO duplicate in statevisualization
    private SetOfTerm getReferences(ListOfTerm terms) {
        // ListOfTerm pc = itNode.getPc();
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        for (IteratorOfTerm it = terms.iterator(); it.hasNext();) {
            result = result.union(getReferences2(it.next()));
        }
        return result;
    }

    private SetOfTerm getReferences2(Term t) {
        // System.out.println(t);
        // if (t.sort()!= Sort.FORMULA && !this.isBool(t)&&!this.isInt(t))

        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        if (referenceSort(t.sort()))
            result = result.add(t);
        for (int i = 0; i < t.arity(); i++) {
            result = result.union(getReferences2(t.sub(i)));
        }
        return result;
    }

    private int getSerialNumber(SetOfTerm refs) {
        int current = -1;

        for (IteratorOfTerm it = refs.iterator(); it.hasNext();) {
            final Term t = it.next();
            if (ref2ser.containsKey(t)
                    && ((current == -1) || ref2ser.get(t)
                            .intValue() < current)) {
                current = ref2ser.get(t).intValue();
            }
        }

        return current;
    }

    private Set<Type> getStaticClasses() {
        HashSet<Type> res = new HashSet<Type>();
        for (IteratorOfTerm it = this.pc.iterator(); it.hasNext();) {
            Term t = it.next();
            res.addAll(this.getStaticClasses(t));

        }

        return res;
    }

    private Set<Type> getStaticClasses(Term t) {
        Set<Type> result = new HashSet<Type>();
        if (t.op() instanceof ProgramVariable) {
            if (((ProgramVariable) t.op()).getContainerType() != null)
                if (!((ProgramVariable) t.op()).isImplicit()
                        || VisualDebugger.showImpliciteAttr)
                    result.add(((ProgramVariable) t.op()).getContainerType()
                            .getJavaType());

        }

        for (int i = 0; i < t.arity(); i++) {
            result.addAll(getStaticClasses(t.sub(i)));
        }
        return result;

    }

    private SymbolicObject getStaticObject(ClassType ct, LinkedList<SymbolicObject> objects) {
        final Iterator<SymbolicObject> it = objects.iterator();
        while (it.hasNext()) {
            final SymbolicObject so = it.next();
            if (so.isStatic() && so.getType().equals(ct))
                return so;
        }
        return null;
    }

    public LinkedList<SymbolicObject> getSymbolicObjects() {
        return symbolicObjects;
    }

    // TODO duplicate in prooflistener

    private void prepare(ITNode itNode, Services serv, ListOfTerm pc,
            SetOfTerm refInPc) {

        this.vd = VisualDebugger.getVisualDebugger();
        this.pc = pc;
        this.node = itNode.getNode();
        this.itNode = itNode;
        this.serv = serv;

        ante = SLListOfTerm.EMPTY_LIST;
        for (final ConstrainedFormula cfma : node.sequent().antecedent()) {
            ante = ante.append(cfma.formula());
        }
        
        
        succ = SLListOfTerm.EMPTY_LIST;
        for (final ConstrainedFormula cfma : node.sequent().succedent()) {
            succ = succ.append(cfma.formula());
        }

        for (final Term instanceTerm :  instanceConfiguration) {
            if (instanceTerm.op() == Op.NOT)
                succ = succ.append(instanceTerm.sub(0));
            else
                ante = ante.append(instanceTerm);
        }

        this.refInPC = refInPc;

        createEquivalenceClassesAndConstraints();
        
        getEqvClass(nullTerm);
        
        findDisjointClasses();
    }

    private boolean referenceSort(Sort s) {
        JavaInfo info = serv.getJavaInfo();
        KeYJavaType kjt = info.getKeYJavaType(s);
        // System.out.println("KJT "+kjt);
        if (kjt == null)
            return false;
        if (kjt.getJavaType() instanceof ClassType)
            return true;

        return false;
    }

    private void setInstanceNames(LinkedList<SymbolicObject> objects) {
        objects = filterStaticObjects(objects);
        ref2ser = new HashMap<Term, Integer>();
        ITNode n = this.itNode;
        while (n.getParent() != null) {
            HashMap<PosInOccurrence, Label> labels = n.getNode()
                    .getNodeInfo().getVisualDebuggerState().getLabels();
            ListOfTerm pc2 = getPc(labels);
            SetOfTerm refs = getReferences(pc2);
            for (IteratorOfTerm it = refs.iterator(); it.hasNext();) {
                Term t = it.next();
                ref2ser.put(t, new Integer(n.getId()));

            }
            n = n.getParent();
        }

        // references in post term
        int j = 0;
        if (postTerms != null)
            for (IteratorOfTerm it = postTerms.iterator(); it.hasNext();) {

                Term t = it.next();
                // System.out.println("pt "+t);
                if (referenceSort(t.sort())) {
                    if (!ref2ser.containsKey(t)) {
                        j++;
                        ref2ser.put(t, new Integer(itNode.getId() + j));

                    }
                }

            }

        VisualDebugger.print("HashMap for Instance Names");

        if (!vd.isStaticMethod())
            ref2ser.put(vd.getInputPV2term().get(
                    TermFactory.DEFAULT.createVariableTerm(vd.getSelfPV())),
                    new Integer(1));

        VisualDebugger.print(ref2ser);

        // System.out.println("INPUT VALUES"+inputVal);

        Iterator<SymbolicObject> it2 = objects.iterator();
        while (it2.hasNext()) {
            SymbolicObject so = it2.next();
            so.setId(getSerialNumber(so.getTerms()));
        }

        SymbolicObject[] sos = objects
                .toArray(new SymbolicObject[objects.size()]);

        // sort symbolic objects according to their ids
        sort(sos);

        HashMap<ClassType, Integer> counters = new HashMap<ClassType, Integer>();

        for (int i = 0; i < sos.length; i++) {
            SymbolicObject so = sos[i];

            if (so.getId() == -1)
                continue;

            Integer newValue;
            if (counters.containsKey(so.getType())) {
                Integer value = counters.get(so.getType());
                newValue = new Integer(value.intValue() + 1);
                counters.remove(so.getType());
                counters.put(so.getType(), newValue);
            } else {
                newValue = new Integer(0);
                counters.put(so.getType(), newValue);

            }

            // instanceName+=newValue.intValue();

            // so.setName(instanceName);

            so.setId(newValue.intValue());

        }

    }

    private void setMethodStack(boolean pre) {
        try {
            final ITNode it = itNode.getMethodNode();
            if (it == null) {
                return;
            }

            MethodBodyStatement mbs = // vd.getLastMethodBodyStatement(itNode.getNode());
            (MethodBodyStatement) it.getActStatement();
            // MethodBodyStatement mbs =
            // vd.getLastMethodBodyStatement(itNode.getNode());
            if (mbs == null)
                return;
            ReferencePrefix refPre = mbs.getMethodReference()
                    .getReferencePrefix();
            SymbolicObject so;

            if (refPre instanceof TypeRef) {
                final KeYJavaType kjt = ((TypeRef) refPre).getKeYJavaType();
                final ClassType type = (ClassType) kjt.getJavaType();
                so = getStaticObject(type, symbolicObjects);
                if (so == null) {
                    so = new SymbolicObject(type, serv);
                    symbolicObjects.add(so);
                }

                so.setMethod(mbs.getProgramMethod(serv));

            } else {

                final Term t = serv.getTypeConverter().convertToLogicElement(
                        refPre);
                methodReferences = new Term[1];
                methodReferences[0] = t;
                HashMap<Operator, Term> map = new HashMap<Operator, Term>();
                Term self = vd.getSelfTerm();
                // vd.getSelfTerm() //TODO
                // ProgramVariable val =
                // (ProgramVariable)((Term)vd.getInputPV2term().get(self)).op();
                Term val = ((Term) vd.getInputPV2term().get(self));
                map.put(self.op(), val);
                ProgVarReplacer pvr = new ProgVarReplacer(map,serv);
                Term res = pvr.replace(t);

                so = getObject(res, symbolicObjects);
                so.setMethod(mbs.getProgramMethod(serv));

            }

            // ArrayOfExpression aof = mbs.getArguments();;
            HashSet set = vd.getParam(mbs);
            ListOfProgramVariable inputPara = vd
                    .arrayOfExpression2ListOfProgVar(mbs.getArguments(), 0);
            ProgramVariable[] inputParaArray = inputPara.toArray();

            ArrayOfParameterDeclaration paraDecl = mbs.getProgramMethod(serv)
                    .getParameters();

            final HashMap<Term,Term> values = vd.getValuesForLocation(set, vd
                    .getProgramPIO(itNode.getNode().sequent()));

            ListOfProgramVariable paramDeclAsPVList = SLListOfProgramVariable.EMPTY_LIST;

            for (int i = 0; i < paraDecl.size(); i++) {
                ProgramVariable next = (ProgramVariable) paraDecl
                        .getParameterDeclaration(i).getVariableSpecification()
                        .getProgramVariable();
                Term val = (Term) values.get(TermFactory.DEFAULT
                        .createVariableTerm(inputParaArray[i]));// TODO
                so.addPara2Value(next, val);
                paramDeclAsPVList = paramDeclAsPVList.append(next);
            }
            so.setParameter(paramDeclAsPVList);

        } catch (Exception e) {
            return;

        }

    }

    /**
     * sort the given array in order of the symbolic objects ids
     * @param a the SymbolicObject array to sort
     */
    private void sort(SymbolicObject a[]) {
        final Comparator<SymbolicObject> comparator = new Comparator<SymbolicObject>() {
            public int compare(SymbolicObject o1, SymbolicObject o2) {
                if (o1.getId() < o2.getId()) {
                    return -1;
                } else if (o1.getId() > o2.getId()) {
                    return 1;
                } else {
                    return 0;
                }
            }
            
        };        
        Arrays.sort(a, comparator);                       
    }

    private class EquClass {
        private SetOfTerm disjointRep = SetAsListOfTerm.EMPTY_SET;

        private SetOfTerm members;

        public EquClass(SetOfTerm members) {
            this.members = members;
        }

        public EquClass(Term t) {
            this(SetAsListOfTerm.EMPTY_SET.add(t));
        }

        public EquClass(Term t1, Term t2) {
            this(SetAsListOfTerm.EMPTY_SET.add(t1).add(t2));
        }

        public void add(EquClass ec) {
            members = members.union(ec.getMembers());
        }

        public void add(Term t) {
            members = members.add(t);
        }

        public void addDisjoint(Term t) {
            disjointRep = disjointRep.add(t);
        }

        public boolean equals(Object o) {
            if (!(o instanceof EquClass)) {
                return false;
            }
            EquClass eqc = (EquClass) o;
            if (eqc.members.size() != members.size()) {
                return false;
            }
            IteratorOfTerm it = members.iterator();
            l: while (it.hasNext()) {
                IteratorOfTerm it2 = eqc.members.iterator();
                Term t = it.next();
                while (it2.hasNext()) {
                    if (t.toString().equals(it2.next().toString())) {
                        continue l;
                    }
                }
                return false;
            }
            return true;
        }

        public SetOfTerm getDisjoints() {
            return disjointRep;
        }

        public KeYJavaType getKeYJavaType() {
            final IteratorOfTerm it = members.iterator();
            Sort s = it.next().sort();
            while (it.hasNext()) {
                final Sort s1 = it.next().sort();
                if (s1.extendsTrans(s)) {
                    s = s1;
                }
            }
            KeYJavaType result = serv.getJavaInfo().getKeYJavaType(s);
            if (result == null && isInt(s)) {
                result = serv.getJavaInfo().getKeYJavaType(
                        serv.getTypeConverter().getIntLDT().targetSort());
            }
            return result;
        }

        /**
         * Returns the locations that are members of this equivalence class.
         */
        public SetOfTerm getLocations() {
            SetOfTerm locations = SetAsListOfTerm.EMPTY_SET;
            IteratorOfTerm it = members.iterator();
            while (it.hasNext()) {
                Term t = it.next();
                if (ModelGenerator.isLocation(t, serv)) {
                    locations = locations.add(t);
                }
            }
            return locations;
        }

        public SetOfTerm getMembers() {
            return members;
        }

        public boolean isArray() {
            for (IteratorOfTerm it = members.iterator(); it.hasNext();) {
                Term t = it.next();
                return isArraySort(t.sort());
            }
            return false;
        }

        private boolean isArraySort(Sort s) {

            return (s instanceof ArraySort);
        }

        public boolean isBoolean() {
            for (IteratorOfTerm it = members.iterator(); it.hasNext();) {
                if (serv.getTypeConverter().getBooleanLDT().targetSort() == it
                        .next().sort()) {
                    return true;
                }
            }
            return false;
        }

        public boolean isInt() {
            for (IteratorOfTerm it = members.iterator(); it.hasNext();) {
                Term t = it.next();
                return isInt(t.sort());
            }
            return false;
        }

        private boolean isInt(Sort s) {
            return s.extendsTrans(serv.getTypeConverter().getIntegerLDT()
                    .targetSort());
        }

        public String toString() {
            return "EquClass: (" + members + ")  Disjoint + "
                    + this.disjointRep + " /";
        }

    }
}
