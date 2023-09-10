/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.UnaryOperator;

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

import org.key_project.util.collection.ImmutableSLList;


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
     * The KeYJavaType representing the function to which the class invariant belongs.
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
     * Whether the class invariant is a static (i.e., &lt;$inv&gt;) or an instance invariant (i.e.,
     * &lt;inv&gt;).
     */
    private final boolean isStatic;
    /**
     * Whether the class invariant is free.
     */
    private final boolean isFree;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates a class invariant.
     *
     * @param name the unique internal name of the invariant
     * @param displayName the displayed name of the invariant
     * @param kjt the KeYJavaType to which the invariant belongs
     * @param visibility the visibility of the invariant (null for default visibility)
     * @param inv the invariant formula itself
     * @param selfVar the variable used for the receiver object
     */
    public ClassInvariantImpl(String name, String displayName, KeYJavaType kjt,
            VisibilityModifier visibility, Term inv, ParsableVariable selfVar) {
        this(name, displayName, kjt, visibility, inv, selfVar, false);
    }

    /**
     * Creates a class invariant.
     *
     * @param name the unique internal name of the invariant
     * @param displayName the displayed name of the invariant
     * @param kjt the KeYJavaType to which the invariant belongs
     * @param visibility the visibility of the invariant (null for default visibility)
     * @param inv the invariant formula itself
     * @param selfVar the variable used for the receiver object
     * @param free whether this contract is free.
     */
    public ClassInvariantImpl(String name, String displayName, KeYJavaType kjt,
            VisibilityModifier visibility, Term inv, ParsableVariable selfVar,
            boolean free) {
        assert name != null && !name.equals("");
        assert displayName != null && !displayName.equals("");
        assert kjt != null;
        assert inv != null;
        this.name = name;
        this.displayName = displayName;
        this.kjt = kjt;
        this.visibility = visibility;
        this.originalInv = inv;
        this.originalSelfVar = selfVar;
        final OpCollector oc = new OpCollector();
        originalInv.execPostOrder(oc);
        this.isStatic = selfVar == null;
        this.isFree = free;
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private Map<Operator, Operator> getReplaceMap(ParsableVariable selfVar, TermServices services) {
        Map<Operator, Operator> result = new LinkedHashMap<>();

        if (selfVar != null && originalSelfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
            result.put(originalSelfVar, selfVar);
        }

        return result;
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public ClassInvariant map(UnaryOperator<Term> op, Services services) {
        return new ClassInvariantImpl(name, displayName, kjt, visibility, op.apply(originalInv),
            originalSelfVar, isFree);
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
        final Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, services);
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
    public boolean isFree() {
        return isFree;
    }


    @Override
    public VisibilityModifier getVisibility() {
        return visibility;
    }


    @Override
    public ClassInvariant setKJT(KeYJavaType newKjt) {
        String newName = name.replaceFirst(kjt.getName(), newKjt.getName());
        return new ClassInvariantImpl(newName, displayName, newKjt, visibility, originalInv,
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
            self = (ProgramVariable) this.originalSelfVar;
        } else if (this.originalSelfVar != null) {
            self = new LocationVariable(new ProgramElementName(originalSelfVar.toString()), kjt);
        } else {
            self = null;
        }
        return new OriginalVariables(self, null, null,
            new LinkedHashMap<>(),
            ImmutableSLList.nil());
    }
}
