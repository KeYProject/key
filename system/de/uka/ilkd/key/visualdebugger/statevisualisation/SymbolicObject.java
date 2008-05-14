package de.uka.ilkd.key.visualdebugger.statevisualisation;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.NullType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class SymbolicObject {

    private final HashMap<IProgramVariable, SymbolicObject> associations = new HashMap<IProgramVariable, SymbolicObject>();

    private final HashMap<ProgramVariable, ListOfTerm> attr2Constraint = new HashMap<ProgramVariable, ListOfTerm>();

    private HashMap<ProgramVariable, Term> attr2ValueTerm = new HashMap<ProgramVariable, Term>();

    private int id;

    private String instanceName;

    private boolean isStatic = false;

    private ProgramMethod method = null;

    private HashMap<ProgramVariable, ListOfTerm> par2constraint = new HashMap<ProgramVariable, ListOfTerm>();

    private HashMap<ProgramVariable, Object> par2value = new HashMap<ProgramVariable, Object>();

    private ListOfProgramVariable parameter;

    private final SetOfTerm terms;

    private final ClassType type;

    private boolean unknownObject = false;

    VisualDebugger vd = VisualDebugger.getVisualDebugger();

    public SymbolicObject(ClassType t, Services s) {
        this.type = t;
        this.terms = SetAsListOfTerm.EMPTY_SET;
        this.isStatic = true;
        this.computeInstanceName();
    }

    public SymbolicObject(SetOfTerm cl, ClassType t, Services s) {
        this.terms = cl;
        assert cl != null && t != null && s != null;
        type = t;
        computeInstanceName();
    }

    public SymbolicObject(Term cl, ClassType t, Services s) {
        this(SetAsListOfTerm.EMPTY_SET.add(cl), t, s);
    }

    public SymbolicObject(Term cl, ClassType t, Services s, boolean unKnown) {
        this(SetAsListOfTerm.EMPTY_SET.add(cl), t, s);
        this.unknownObject = unKnown;
    }

    public void addAssociation(IProgramVariable f, SymbolicObject o) {
        associations.put(f, o);

    }

    public void addAttributeConstraint(ProgramVariable f, Term o) {
        if (attr2Constraint.containsKey(f)) {
            ListOfTerm t = attr2Constraint.get(f);
            t = t.append(o);
            attr2Constraint.remove(f);
            attr2Constraint.put(f, t);

        } else {
            ListOfTerm t = SLListOfTerm.EMPTY_LIST.append(o);
            attr2Constraint.put(f, t);
        }

    }

    /**
     * 
     * @param par
     *                parameter pv
     * @param value
     *                instanceof SymbolicObject or Term
     */
    public void addPara2Value(ProgramVariable par, Object value) {
        this.par2value.put(par, value);
    }

    public void addParameterConstraint(ProgramVariable f, ListOfTerm o) {
        if (this.par2constraint.containsKey(f)) {
            ListOfTerm t = par2constraint.get(f);
            t = t.append(o);
            par2constraint.remove(f);
            par2constraint.put(f, t);
        } else {
            ListOfTerm t = SLListOfTerm.EMPTY_LIST.append(o);
            par2constraint.put(f, t);
        }
    }

    public void addParameterConstraint(ProgramVariable f, Term o) {
        if (this.par2constraint.containsKey(f)) {
            ListOfTerm t = par2constraint.get(f);
            t = t.append(o);
            par2constraint.remove(f);
            par2constraint.put(f, t);
        } else {
            ListOfTerm t = SLListOfTerm.EMPTY_LIST.append(o);
            par2constraint.put(f, t);
        }
    }

    public void addValueTerm(ProgramVariable pv, Term val) {
        attr2ValueTerm.put(pv, val);
    }

    private void computeInstanceName() {
        if (isStatic()) {
            this.instanceName = "<Class>";

        } else if (!vd.isStaticMethod()
                && terms.contains((Term) VisualDebugger.getVisualDebugger()
                        .getInputPV2term().get(vd.getSelfTerm()))) {
            this.instanceName = "self";

        } else if (id == -1) {

        }

        else {
            final String className = getType().getName().toString();
            final String b = className.substring(0, 1).toLowerCase();
            instanceName = b + className.substring(1, className.length());
            instanceName += "_" + id;
        }
    }

    public Collection<SymbolicObject> getAllAssociationEnds() {
        return this.associations.values();

    }

    public SetOfProgramVariable getAllModifiedPrimitiveAttributes() {
        SetOfProgramVariable result = SetAsListOfProgramVariable.EMPTY_SET;
        Set<ProgramVariable> s = attr2ValueTerm.keySet();
        for (Iterator<ProgramVariable> it = s.iterator(); it.hasNext();) {
            result = result.add(it.next());
        }
        return result;
    }

    public SymbolicObject getAssociationEnd(ProgramVariable f) {
        return associations.get(f);
    }

    public ListOfTerm getAttrConstraints(ProgramVariable f) {
        return attr2Constraint.get(f);
    }

    public SetOfProgramVariable getAttributes() {
        SetOfProgramVariable result = SetAsListOfProgramVariable.EMPTY_SET;
        Set<ProgramVariable> s = attr2Constraint.keySet();
        for (Iterator<ProgramVariable> it = s.iterator(); it.hasNext();) {
            result = result.add(it.next());
        }
        return result;
    }

    public int getId() {
        return id;
    }

    public String getInstanceName() {
        return this.instanceName;
    }

    public ProgramMethod getMethod() {
        return method;
    }

    public SetOfProgramVariable getNonPrimAttributes() {
        SetOfProgramVariable result = SetAsListOfProgramVariable.EMPTY_SET;
        Set<IProgramVariable> s = associations.keySet();
        for (Iterator<IProgramVariable> it = s.iterator(); it.hasNext();) {
            result = result.add((ProgramVariable) it.next());
        }
        return result;
    }

    public ListOfTerm getParaConstraints(ProgramVariable f) {
        return this.par2constraint.get(f);
    }

    public ListOfProgramVariable getParameter() {
        return parameter;
    }

    // ------------------------------------------------------------------
    // Methods for post state

    public SetOfTerm getTerms() {
        return terms;
    }

    public ClassType getType() {
        return type;
    }

    /**
     * 
     * @param para
     * @return instanceof SymbolicObject or Term
     */
    public Term getValueOfParameter(ProgramVariable para) {
        return (Term) par2value.get(para);

    }

    public Term getValueTerm(ProgramVariable pv) {
        return this.attr2ValueTerm.get(pv);
    }

    public boolean isNull() {
        return (type instanceof NullType);
    }

    public boolean isStatic() {
        return isStatic;
    }

    public boolean isUnknownObject() {
        return unknownObject;
    }

    // public void setName(String name) {
    // this.name = name;
    // }
    //    
    public void setId(int id) {
        this.id = id;
        this.computeInstanceName();
    }

    public void setMethod(ProgramMethod method) {
        this.method = method;
    }

    public void setParameter(ListOfProgramVariable parameter) {
        this.parameter = parameter;
    }

    public String toString() {
        String result = "Symbolic Object " + this.instanceName + " ";
        result += "Members " + terms;

        return result;

    }

}
