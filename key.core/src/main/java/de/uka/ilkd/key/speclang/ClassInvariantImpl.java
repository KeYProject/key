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

package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;


/**
 * Standard implementation of the ClassInvariant interface.
 */
public final class ClassInvariantImpl implements ClassInvariant {

    /**
     * The unique internal name of the class invariant.
     */
    private final String name;
    /**
     * The displayed name.
     */
    private final String displayName;
    /**
     * The KeYJavaType representing the function to which the
     * class invariant belongs.
     */
    private final KeYJavaType kjt;
    /**
     * The visibility of the class invariant (null for default visibility).
     */
    private final VisibilityModifier visibility;
    /**
     * The original invariant from which the class invariant is derived.
     */
    private final Term originalInv;
    /**
     * The original self variable of the receiver object.
     */
    private final ParsableVariable originalSelfVar;
    /**
     * Whether the class invariant is a static (i.e., &lt;$inv&gt;)
     * or an instance invariant (i.e., &lt;inv&gt;).
     */
    private final boolean isStatic;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    /**
     * Creates a class invariant.
     * @param name the unique internal name of the invariant
     * @param displayName the displayed name of the invariant
     * @param kjt the KeYJavaType to which the invariant belongs
     * @param visibility the visibility of the invariant
     *        (null for default visibility)
     * @param inv the invariant formula itself
     * @param selfVar the variable used for the receiver object
     */
    public ClassInvariantImpl(String name,
                              String displayName,
                              KeYJavaType kjt,
                              VisibilityModifier visibility,
                              Term inv,
                              ParsableVariable selfVar) {
        assert name != null && !name.equals("");
        assert displayName != null && !displayName.equals("");
	assert kjt != null;
        assert inv != null;
        this.name            = name;
        this.displayName     = displayName;
	this.kjt             = kjt;
        this.visibility      = visibility;
        this.originalInv     = inv;
        this.originalSelfVar = selfVar;
        final OpCollector oc = new OpCollector();
        originalInv.execPostOrder(oc);
        this.isStatic        = selfVar == null;
//        assert isStatic == !oc.contains(originalSelfVar);
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private Map<Operator, Operator> getReplaceMap(
                ParsableVariable selfVar,
                TermServices services) {
        Map<Operator, Operator> result = new LinkedHashMap<Operator, Operator>();

        if(selfVar != null && originalSelfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
            result.put(originalSelfVar, selfVar);
        }

        return result;
    }



    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public ClassInvariant map(UnaryOperator<Term> op, Services services) {
        return new ClassInvariantImpl(
                name, displayName, kjt, visibility, op.apply(originalInv), originalSelfVar);
    }

    @Override
    public String getName() {
        return name;
    }


    @Override
    public String getDisplayName() {
        return displayName;
    }


    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }


    @Override
    public Term getInv(ParsableVariable selfVar, TermServices services) {
        final Map<Operator, Operator> replaceMap
        	= getReplaceMap(selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        Term res = or.replace(originalInv);
        res = services.getTermBuilder().convertToFormula(res);
        return res;
    }


    @Override
    public Term getOriginalInv() {
        return originalInv;
    }


    @Override
    public boolean isStatic() {
	return isStatic;
    }


    @Override
    public VisibilityModifier getVisibility() {
	return visibility;
    }


    @Override
    public ClassInvariant setKJT(KeYJavaType newKjt) {
        String newName = name.replaceFirst(kjt.getName(), newKjt.getName());
        return new ClassInvariantImpl(newName,
                                      displayName,
                                      newKjt,
                                      visibility,
                                      originalInv,
                                      originalSelfVar);
    }


    @Override
    public String toString() {
        return originalInv.toString();
    }

    @Override
    public OriginalVariables getOrigVars() {
        final ProgramVariable self;
        if (this.originalSelfVar instanceof ProgramVariable) {
            self = (ProgramVariable)this.originalSelfVar;
        } else if(this.originalSelfVar != null) {
            self = new LocationVariable(
                    new ProgramElementName(originalSelfVar.toString()), kjt);
        } else {
            self = null;
        }
        return new OriginalVariables(self, null, null,
                new LinkedHashMap<LocationVariable, ProgramVariable>(),
                ImmutableSLList.<ProgramVariable>nil());
    }
}