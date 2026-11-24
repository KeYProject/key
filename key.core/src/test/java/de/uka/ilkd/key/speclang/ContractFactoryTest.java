/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.nio.file.Path;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * This class holds tests for the ContractFactory.
 *
 * @author Wolfram Pfeifer
 */
public class ContractFactoryTest {
    /**
     * the filename of the key file which is needed to create Services and JavaInfo
     */
    private static final Path TEST_FILE = HelperClassForTests.TESTCASE_DIRECTORY
            .resolve("speclang").resolve("testFile.key");

    /** JavaInfo containing information about the available datatypes and methods */
    private JavaInfo javaInfo;

    /** services needed for translation */
    private Services services;

    /** context information needed for JmlIO/parser */
    private KeYJavaType testClassType;

    /**
     * Creates the JavaInfo and Services.
     */
    @BeforeEach
    public synchronized void setUp() {
        if (javaInfo == null) {
            javaInfo = HelperClassForTests.parse(TEST_FILE).getFirstProof().getJavaInfo();
            services = javaInfo.getServices();
            services.setOriginFactory(new OriginTermLabelFactory());
            testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
        }
    }

    /**
     * Checks that two equal assignable clauses are combined correctly, i.e., without
     * if-expressions.
     *
     * @throws SLTranslationException
     *         is not thrown if the test succeeds
     */
    @Test
    public void testCombineEqualModifiable() throws SLTranslationException {
        JTerm woLabels =
            calculateCombinedModifiableWOLabels("\\nothing", "\\nothing");
        assertEquals("empty<Pair<java.lang.Object,Field>>", woLabels.toString());
    }

    /**
     * Checks that two different assignable clauses are combined correctly: \nothing and
     * \strictly_nothing should be combined to empty (w/o if-then-else).
     *
     * @throws SLTranslationException
     *         is not thrown if test succeeds
     */
    @Test
    public void testCombineEmptyModifiable() throws SLTranslationException {
        JTerm woLabels =
            calculateCombinedModifiableWOLabels("\\strictly_nothing", "\\nothing");
        assertEquals("empty<Pair<java.lang.Object,Field>><<impl>>", woLabels.toString());
    }

    /**
     * Checks that two different assignable clauses are combined correctly, i.e. using intersection
     * and if-expressions with preconditions of the original contracts in their conditions.
     *
     * @throws SLTranslationException
     *         is not thrown if test succeeds
     */
    @Test
    public void testCombineDifferentModifiable() throws SLTranslationException {
        JTerm woLabels =
            calculateCombinedModifiableWOLabels("l", "\\nothing");
        assertEquals(
            "intersect<Pair<java.lang.Object,Field>>(if-then-else(equals(a,Z(5(#))),empty<Pair<java.lang.Object,Field>>,allLocs),"
                + "if-then-else(not(equals(a,Z(5(#)))),singleton<Pair<java.lang.Object,Field>>(pair<java.lang.Object,Field>(self,testPackage.TestClass::#l)),"
                + "allLocs))",
            woLabels.toString());
    }

    /**
     * Helper for the tests: Builds two operation contracts for method {@code m} - a normal and an
     * exceptional one with the given assignable clauses - combines them and returns the modifiable
     * term of the resulting combined contract (with origin labels removed).
     *
     * @param normalAssignable
     *        the assignable clause of the normal behavior contract
     * @param exceptionalAssignable
     *        the assignable clause of the exceptional behavior contract
     * @return the combined modifiable term of the contracts, without origin labels
     * @throws SLTranslationException
     *         should not be thrown
     */
    private JTerm calculateCombinedModifiableWOLabels(String normalAssignable,
            String exceptionalAssignable) throws SLTranslationException {
        JMLSpecFactory jsf = new JMLSpecFactory(services);

        ImmutableList<KeYJavaType> signature = ImmutableList.nil();
        signature = signature.append(javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT));
        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        TextualJMLSpecCase normal =
            new TextualJMLSpecCase(ImmutableList.nil(), Behavior.NORMAL_BEHAVIOR);
        normal.addClause(ClauseHd.REQUIRES, JmlFacade.parseClause("requires a != 5;"));
        normal.addClause(ClauseHd.ENSURES, JmlFacade.parseClause("ensures \\result == 3;"));
        normal.addClause(ClauseHd.ASSIGNABLE,
            JmlFacade.parseClause("assignable " + normalAssignable + ";"));

        TextualJMLSpecCase exceptional =
            new TextualJMLSpecCase(ImmutableList.nil(), Behavior.EXCEPTIONAL_BEHAVIOR);
        exceptional.addClause(ClauseHd.REQUIRES, JmlFacade.parseClause("requires a == 5;"));
        exceptional.addClause(ClauseHd.ASSIGNABLE,
            JmlFacade.parseClause("assignable " + exceptionalAssignable + ";"));
        exceptional.addClause(Clause.SIGNALS,
            JmlFacade.parseClause("signals (RuntimeException e) true;"));
        exceptional.addClause(Clause.SIGNALS_ONLY,
            JmlFacade.parseClause("signals_only RuntimeException;"));

        ImmutableSet<Contract> contractSet = ImmutableSet.empty();
        contractSet = contractSet.union(jsf.createJMLOperationContracts(pm, normal));
        contractSet = contractSet.union(jsf.createJMLOperationContracts(pm, exceptional));
        assertEquals(2, contractSet.size());

        FunctionalOperationContract[] cs = new FunctionalOperationContract[contractSet.size()];
        int i = 0;
        for (Contract c : contractSet) {
            cs[i] = (FunctionalOperationContract) c;
            i++;
        }

        // combine exceptional with normal contract
        ContractFactory cf = new ContractFactory(services);
        FunctionalOperationContract singleContract = cf.union(cs);

        // remove origin labels
        JTerm combinedModifiable = singleContract.getModifiable();
        return TermLabelManager.removeIrrelevantLabels(combinedModifiable, services);
    }
}
