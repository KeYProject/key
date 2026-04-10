/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static org.junit.jupiter.api.Assertions.*;

public class TestApplyUpdateOnRigidCondition {

    private static MatchResultInfo EMPTY_MATCHCONDITIONS =
        de.uka.ilkd.key.rule.MatchConditions.EMPTY_MATCHCONDITIONS;

    @Test
    void updateWithoutVariables() {
        JTerm term = TacletForTests.parseTerm("{i:=0}\\forall int a; a = i");
        JTerm result = applyUpdateOnFormula(term);
        JTerm expected = TacletForTests.parseTerm("\\forall int a; {i:=0}(a = i)");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Update without free variables was not properly applied on formula!");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (0)");

        term = TacletForTests.parseTerm("{i:=0}(i = 0)");
        result = applyUpdateOnFormula(term);
        expected = TacletForTests.parseTerm("{i:=0} i = {i:=0} 0");
        assertEquals(expected, result,
            "Update without free variables was not properly applied on formula!");

        term = TacletForTests.parseTerm("{i:=0} f(const)");
        result = applyUpdateOnTerm(term);
        expected = TacletForTests.parseTerm("f({i:=0} const)");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Update without free variables was not properly applied on term!");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (1)");
    }

    @Test
    void updateWithVariablesNoClash() {
        TermBuilder tb = TacletForTests.services().getTermBuilder();

        JTerm term =
            TacletForTests.parseTerm("\\forall int b; {i:=b}\\forall java.lang.Object a; a = i");
        QuantifiableVariable b = term.boundVars().get(0);
        JTerm result = tb.all(b, applyUpdateOnFormula(term.sub(0)));
        JTerm expected =
            TacletForTests.parseTerm("\\forall int b; \\forall java.lang.Object a; {i:=b} (a = i)");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Update is not simply pulled over quantification!");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (0)");

        term = TacletForTests.parseTerm("\\forall int b; {i:=b} (0 = i)");
        b = term.boundVars().get(0);
        result = tb.all(b, applyUpdateOnFormula(term.sub(0)));
        expected = TacletForTests.parseTerm("\\forall int b; {i:=b} 0 = {i:=b} i");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Update is not simply pulled over equality!");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (1)");

        term = TacletForTests.parseTerm("\\forall int b; {i:=b} f(const) = 0");
        b = term.boundVars().get(0);
        result = tb.all(b, tb.equals(applyUpdateOnTerm(term.sub(0).sub(0)), term.sub(0).sub(1)));
        expected = TacletForTests.parseTerm("\\forall int b; f({i:=b} const) = 0");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Update is not simply pulled over function symbol!");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (2)");
    }

    @Test
    void updateWithVariablesAndClash() {
        TermBuilder tb = TacletForTests.services().getTermBuilder();

        JTerm term =
            TacletForTests.parseTerm("\\forall int a; {i:=a}\\forall java.lang.Object a; a = i");
        QuantifiableVariable a = term.boundVars().get(0);
        JTerm result = tb.all(a, applyUpdateOnFormula(term.sub(0)));
        JTerm expected = TacletForTests
                .parseTerm("\\forall int a; \\forall java.lang.Object a1; {i:=a} (a1 = i)");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Renaming or applying update afterwards !");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (0)");

        term = TacletForTests.parseTerm(
            "\\forall int a1; \\forall int a; {i:=a}\\forall java.lang.Object a; i = a1");
        a = term.boundVars().get(0);
        QuantifiableVariable a1 = term.sub(0).boundVars().get(0);
        result = tb.all(a, tb.all(a1, applyUpdateOnFormula(term.sub(0).sub(0))));
        expected = TacletForTests.parseTerm(
            "\\forall int a1; \\forall int a; \\forall java.lang.Object a2; {i:=a} (i = a1)");
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(expected, result),
            "Counter appended to stem was not increased high enough!");
        assertEquals(expected.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            result.hashCodeModProperty(RENAMING_TERM_PROPERTY),
            "Terms should be equal modulo renaming. (1)");
    }

    @Test
    void notRigid() {
        JTerm term = TacletForTests.parseTerm("{i:=0} i");
        JTerm result = applyUpdateOnTerm(term);
        JTerm expected = TacletForTests.parseTerm("{i:=0} i");
        assertEquals(expected, result,
            "The term should not change, as the update should not be applied");
    }

    @Test
    void arityZero() {
        JTerm term = TacletForTests.parseTerm("{i:=0} A");
        JTerm result = applyUpdateOnFormula(term);
        JTerm expected = TacletForTests.parseTerm("{i:=0} A");
        assertEquals(expected, result,
            "The term should not change, as the update should not be applied");

        term = TacletForTests.parseTerm("{i:=0} const");
        result = applyUpdateOnTerm(term);
        expected = TacletForTests.parseTerm("{i:=0} const");
        assertEquals(expected, result,
            "The term should not change, as the update should not be applied");
    }

    @Test
    void uninstantiatedSV() {
        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable phi = SchemaVariableFactory.createFormulaSV(new Name("phi"));
        SchemaVariable result = SchemaVariableFactory.createFormulaSV(new Name("result"));

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        MatchResultInfo mc = EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        ApplyUpdateOnRigidCondition cond = new ApplyUpdateOnRigidCondition(u, phi, result);

        // u uninstantiated
        mc = cond.check(null, null, mc, TacletForTests.services());
        assert mc != null;
        assertEquals(svInst, mc.getInstantiations());

        JTerm update = TacletForTests.parseTerm("{i:=0}0").sub(0);
        svInst = svInst.add(u, update, TacletForTests.services());
        mc = EMPTY_MATCHCONDITIONS.setInstantiations(svInst);

        mc = cond.check(null, null, mc, TacletForTests.services());
        assert mc != null;
        // phi uninstantiated
        assertEquals(svInst, mc.getInstantiations());
    }

    @Test
    void preInstantiatedResultMatching() {
        JTerm term = TacletForTests.parseTerm("{i:=0}(i = 0)");
        JTerm preInstResult = TacletForTests.parseTerm("{i:=0} i = {i:=0} 0");

        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable phi = SchemaVariableFactory.createFormulaSV(new Name("phi"));
        SchemaVariable result = SchemaVariableFactory.createFormulaSV(new Name("result"));

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        svInst = svInst.add(u, term.sub(0), TacletForTests.services());
        svInst = svInst.add(phi, term.sub(1), TacletForTests.services());
        svInst = svInst.add(result, preInstResult, TacletForTests.services());

        MatchResultInfo mc = EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        ApplyUpdateOnRigidCondition cond = new ApplyUpdateOnRigidCondition(u, phi, result);

        mc = cond.check(null, null, mc, TacletForTests.services());
        assert mc != null;
        assertEquals(svInst, mc.getInstantiations());
    }

    @Test
    void preInstantiatedResultNotMatching() {
        JTerm term = TacletForTests.parseTerm("{i:=0}(i = 0)");
        JTerm preInstWrongResult = TacletForTests.parseTerm("i = 0");

        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable phi = SchemaVariableFactory.createFormulaSV(new Name("phi"));
        SchemaVariable result = SchemaVariableFactory.createFormulaSV(new Name("result"));

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        svInst = svInst.add(u, term.sub(0), TacletForTests.services());
        svInst = svInst.add(phi, term.sub(1), TacletForTests.services());
        svInst = svInst.add(result, preInstWrongResult, TacletForTests.services());

        MatchResultInfo mc = EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        ApplyUpdateOnRigidCondition cond = new ApplyUpdateOnRigidCondition(u, phi, result);

        mc = cond.check(null, null, mc, TacletForTests.services());
        assertNull(mc,
            "MatchConditions were returned, even though the instantiated result should not match the proper result instantiation");
    }

    /**
     * Uses the {@link ApplyUpdateOnRigidCondition} to apply the update on the formula. If the
     * update cannot be applied,
     * the original formula is returned.
     *
     * @param term the {@link JTerm} that must be an update applied on a formula
     * @return the original formula if the update cannot be applied; else, the updated formula is
     *         returned
     */
    private JTerm applyUpdateOnFormula(JTerm term) {
        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable phi = SchemaVariableFactory.createFormulaSV(new Name("phi"));
        SchemaVariable result = SchemaVariableFactory.createFormulaSV(new Name("result"));

        return instantiateAndCheck(term, u, phi, result);
    }

    /**
     * Uses the {@link ApplyUpdateOnRigidCondition} to apply the update on the term. If the update
     * cannot be applied,
     * the original term is returned.
     *
     * @param term the {@link JTerm} that must be an update applied on a formula
     * @return the original term if the update cannot be applied; else, the updated term is returned
     */
    private JTerm applyUpdateOnTerm(JTerm term) {
        Sort sort = term.sub(1).sort();

        UpdateSV u = SchemaVariableFactory.createUpdateSV(new Name("u"));
        SchemaVariable t = SchemaVariableFactory.createTermSV(new Name("t"), sort);
        SchemaVariable result = SchemaVariableFactory.createTermSV(new Name("result"), sort);

        return instantiateAndCheck(term, u, t, result);
    }

    /**
     * Instantiates the given schema variables with the content of <code>term</code>.
     *
     * @param term the {@link JTerm} that must be an update applied on a formula or term
     * @param u the {@link UpdateSV} that is instantiated with the update in <code>term</code>
     * @param tOrPhi the {@link SchemaVariable} that is instantiated with the term or formula in
     *        <code>term</code>
     * @param result the {@link SchemaVariable} that is instantiated with the result of a
     *        {@link ApplyUpdateOnRigidCondition#check(SchemaVariable, SyntaxElement, MatchResultInfo, Services)}
     *        call
     *
     * @return the original formula or term if the update cannot be applied; else, the updated
     *         formula or term is returned
     */
    private JTerm instantiateAndCheck(JTerm term, UpdateSV u, SchemaVariable tOrPhi,
            SchemaVariable result) {
        JTerm update = term.sub(0);
        JTerm arg = term.sub(1);

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        svInst = svInst.add(u, update, TacletForTests.services());
        svInst = svInst.add(tOrPhi, arg, TacletForTests.services());

        ApplyUpdateOnRigidCondition cond = new ApplyUpdateOnRigidCondition(u, tOrPhi, result);
        MatchResultInfo mc = EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        // First two arguments are not used by this check
        mc = cond.check(null, null, mc, TacletForTests.services());

        if (mc == null) {
            return term;
        }

        return ((de.uka.ilkd.key.rule.MatchConditions) mc).getInstantiations()
                .getTermInstantiation(result, null, TacletForTests.services());
    }

}
