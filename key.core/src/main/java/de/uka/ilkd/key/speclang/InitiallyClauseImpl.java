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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;


/**
 * Standard implementation of the InitiallyClause interface.
 *
 * @author Daniel Bruns
 */
public final class InitiallyClauseImpl implements InitiallyClause {

    /**
     * The unique internal name of the initially clause.
     */
    private final String name;
    /**
     * The displayed name.
     */
    private final String displayName;
    /**
     * The KeYJavaType representing the function to which the initially clause belongs.
     */
    private final KeYJavaType kjt;
    /**
     * The visibility of the initially clause (null for default visibility).
     */
    private final VisibilityModifier visibility;
    /**
     * The invariant from which the initially clause is derived.
     */
    private final Term originalInv;
    /**
     * The original self variable of the receiver object.
     */
    private final ParsableVariable originalSelfVar;
    /**
     * The original specification.
     */
    private final LabeledParserRuleContext originalSpec;


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
     * @param originalSpec
     */
    public InitiallyClauseImpl(String name, String displayName, KeYJavaType kjt,
            VisibilityModifier visibility, Term inv, ParsableVariable selfVar,
            LabeledParserRuleContext originalSpec) {
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
        this.originalSpec = originalSpec;
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
    public InitiallyClause map(UnaryOperator<Term> op, Services services) {
        return new InitiallyClauseImpl(name, displayName, kjt, visibility, op.apply(originalInv),
            originalSelfVar, originalSpec);
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
    public Term getClause(ParsableVariable selfVar, TermServices services) {
        final Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        Term res = or.replace(originalInv);
        res = services.getTermBuilder().convertToFormula(res);
        return res;
    }

    @Override
    public LabeledParserRuleContext getOriginalSpec() {
        return originalSpec;
    }

    @Override
    public VisibilityModifier getVisibility() {
        return visibility;
    }

    @Override
    public String toString() {
        return originalInv.toString();
    }

    @Override
    public InitiallyClause setKJT(KeYJavaType newKjt) {
        return new InitiallyClauseImpl(name, displayName, newKjt, visibility, originalInv,
            originalSelfVar, originalSpec);
    }
}
