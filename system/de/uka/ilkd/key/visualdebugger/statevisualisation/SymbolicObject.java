// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger.statevisualisation;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.NullType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class SymbolicObject {

    private final HashMap<IProgramVariable, SymbolicObject> associations = new HashMap<IProgramVariable, SymbolicObject>();

    private final HashMap<ProgramVariable, ImmutableList<Term>> attr2Constraint = new HashMap<ProgramVariable, ImmutableList<Term>>();

    private HashMap<ProgramVariable, Term> attr2ValueTerm = new HashMap<ProgramVariable, Term>();

    private int id;

    private String instanceName;

    private boolean isStatic = false;

    private ProgramMethod method = null;

    private HashMap<ProgramVariable, ImmutableList<Term>> par2constraint = new HashMap<ProgramVariable, ImmutableList<Term>>();

    private HashMap<ProgramVariable, Object> par2value = new HashMap<ProgramVariable, Object>();

    private ImmutableList<ProgramVariable> parameter;

    private final ImmutableSet<Term> terms;

    private final ClassType type;

    private boolean unknownObject = false;

    VisualDebugger vd = VisualDebugger.getVisualDebugger();

    public SymbolicObject(ClassType t, Services s) {
        this.type = t;
        this.terms = DefaultImmutableSet.<Term>nil();
        this.isStatic = true;
        this.computeInstanceName();
    }

    public SymbolicObject(ImmutableSet<Term> cl, ClassType t, Services s) {
        this.terms = cl;
        assert cl != null && t != null && s != null;
        type = t;
        computeInstanceName();
    }

    public SymbolicObject(Term cl, ClassType t, Services s) {
        this(DefaultImmutableSet.<Term>nil().add(cl), t, s);
    }

    public SymbolicObject(Term cl, ClassType t, Services s, boolean unKnown) {
        this(DefaultImmutableSet.<Term>nil().add(cl), t, s);
        this.unknownObject = unKnown;
    }

    public void addAssociation(IProgramVariable f, SymbolicObject o) {
        associations.put(f, o);

    }

    public void addAttributeConstraint(ProgramVariable f, Term o) {
        if (attr2Constraint.containsKey(f)) {
            ImmutableList<Term> t = attr2Constraint.get(f);
            t = t.append(o);
            attr2Constraint.remove(f);
            attr2Constraint.put(f, t);

        } else {
            ImmutableList<Term> t = ImmutableSLList.<Term>nil().append(o);
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

    public void addParameterConstraint(ProgramVariable f, ImmutableList<Term> o) {
        if (this.par2constraint.containsKey(f)) {
            ImmutableList<Term> t = par2constraint.get(f);
            t = t.append(o);
            par2constraint.remove(f);
            par2constraint.put(f, t);
        } else {
            ImmutableList<Term> t = ImmutableSLList.<Term>nil().append(o);
            par2constraint.put(f, t);
        }
    }

    public void addParameterConstraint(ProgramVariable f, Term o) {
        if (this.par2constraint.containsKey(f)) {
            ImmutableList<Term> t = par2constraint.get(f);
            t = t.append(o);
            par2constraint.remove(f);
            par2constraint.put(f, t);
        } else {
            ImmutableList<Term> t = ImmutableSLList.<Term>nil().append(o);
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
                && terms.contains(VisualDebugger.getVisualDebugger()
                        .getInputPV2term().get(vd.getSelfTerm()))) {
            this.instanceName = "self";

        } else if (id == -1) {

        }

        else {
            final String className = getType().getName();
            final String b = className.substring(0, 1).toLowerCase();
            instanceName = b + className.substring(1, className.length());
            instanceName += "_" + id;
        }
    }

    public Collection<SymbolicObject> getAllAssociationEnds() {
        return this.associations.values();

    }

    public ImmutableSet<ProgramVariable> getAllModifiedPrimitiveAttributes() {
        ImmutableSet<ProgramVariable> result = DefaultImmutableSet.<ProgramVariable>nil();
        Set<ProgramVariable> s = attr2ValueTerm.keySet();
        for (ProgramVariable value : s) {
            result = result.add(value);
        }
        return result;
    }

    public SymbolicObject getAssociationEnd(ProgramVariable f) {
        return associations.get(f);
    }

    public ImmutableList<Term> getAttrConstraints(ProgramVariable f) {
        return attr2Constraint.get(f);
    }

    public ImmutableSet<ProgramVariable> getAttributes() {
        ImmutableSet<ProgramVariable> result = DefaultImmutableSet.<ProgramVariable>nil();
        Set<ProgramVariable> s = attr2Constraint.keySet();
        for (ProgramVariable value : s) {
            result = result.add(value);
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

    public ImmutableSet<ProgramVariable> getNonPrimAttributes() {
        ImmutableSet<ProgramVariable> result = DefaultImmutableSet.<ProgramVariable>nil();
        Set<IProgramVariable> s = associations.keySet();
        for (IProgramVariable value : s) {
            result = result.add((ProgramVariable) value);
        }
        return result;
    }

    public ImmutableList<Term> getParaConstraints(ProgramVariable f) {
        return this.par2constraint.get(f);
    }

    public ImmutableList<ProgramVariable> getParameter() {
        return parameter;
    }

    // ------------------------------------------------------------------
    // Methods for post state

    public ImmutableSet<Term> getTerms() {
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

    public void setParameter(ImmutableList<ProgramVariable> parameter) {
        this.parameter = parameter;
    }

    public String toString() {
        String result = "Symbolic Object " + this.instanceName + " ";
        result += "Members " + terms;

        return result;

    }

}
