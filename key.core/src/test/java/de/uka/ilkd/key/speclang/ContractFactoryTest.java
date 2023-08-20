/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.njml.PreParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
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
    /** the filename of the key file which is needed to create Services and JavaInfo */
    private static final String TEST_FILE = HelperClassForTests.TESTCASE_DIRECTORY + File.separator
        + "speclang" + File.separator + "testFile.key";

    /** JavaInfo containing information about the available datatypes and methods */
    private JavaInfo javaInfo;

    /** services needed for translation */
    private Services services;

    /** service for JML translation */
    private PreParser preParser;

    /** context information needed for JmlIO/parser */
    private KeYJavaType testClassType;

    /**
     * Creates the JavaInfo, Services, and JmlIO.
     */
    @BeforeEach
    public synchronized void setUp() {
        if (javaInfo == null) {
            javaInfo =
                new HelperClassForTests().parse(new File(TEST_FILE)).getFirstProof().getJavaInfo();
            services = javaInfo.getServices();
            testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
        }
        preParser = new PreParser();
    }

    /**
     * Checks that two equal assignable clauses are combined correctly, i.e. without if-expressions.
     *
     * @throws SLTranslationException is not thrown if test succeeds
     */
    @Test
    public void testCombineEqualAssignable() throws SLTranslationException {
        String contract = "/*@ normal_behavior\n" + "@  requires a != 5;\n"
            + "@  ensures \\result == 3;\n" + "@  assignable \\nothing;\n" + "@\n" + "@ also\n"
            + "@\n" + "@ exceptional_behavior\n" + "@  requires a == 5;\n"
            + "@  assignable \\nothing;\n" + "@  signals (RuntimeException e) true;\n"
            + "@  signals_only RuntimeException;\n" + "@*/";
        Term woLabels = calculateCombinedModWOLabels(contract);
        assertEquals("empty", woLabels.toString());
    }

    /**
     * Checks that two different assignable clauses are combined correctly: \nothing and
     * \strictly_nothing should be combined to empty (w/o if-then-else).
     *
     * @throws SLTranslationException is not thrown if test succeeds
     */
    @Test
    public void testCombineEmptyAssignable() throws SLTranslationException {
        String contract = "/*@ normal_behavior\n" + "@  requires a != 5;\n"
            + "@  ensures \\result == 3;\n" + "@  assignable \\strictly_nothing;\n" + "@\n"
            + "@ also\n" + "@\n" + "@ exceptional_behavior\n" + "@  requires a == 5;\n"
            + "@  assignable \\nothing;\n" + "@  signals (RuntimeException e) true;\n"
            + "@  signals_only RuntimeException;\n" + "@*/";
        Term woLabels = calculateCombinedModWOLabels(contract);
        assertEquals("empty<<impl>>", woLabels.toString());
    }

    /**
     * Checks that two different assignable clauses are combined correctly, i.e. using intersection
     * and if-expressions with preconditions of the original contracts in their conditions.
     *
     * @throws SLTranslationException is not thrown if test succeeds
     */
    @Test
    public void testCombineDifferentAssignable() throws SLTranslationException {
        String contract = "/*@ normal_behavior\n" + "@  requires a != 5;\n"
            + "@  ensures \\result == 3;\n" + "@  assignable l;\n" + "@\n" + "@ also\n" + "@\n"
            + "@ exceptional_behavior\n" + "@  requires a == 5;\n" + "@  assignable \\nothing;\n"
            + "@  signals (RuntimeException e) true;\n" + "@  signals_only RuntimeException;\n"
            + "@*/";
        Term woLabels = calculateCombinedModWOLabels(contract);
        assertEquals("intersect(if-then-else(equals(a,Z(5(#))),empty,allLocs),"
            + "if-then-else(not(equals(a,Z(5(#)))),singleton(self,testPackage.TestClass::$l),"
            + "allLocs))", woLabels.toString());
    }

    /**
     * Helper for the tests: Parses the given contracts (must always be two), combines them and
     * returns the modifies term of the resulting combined contract (with origin labels removed).
     *
     * @param contractStr the string containing the contracts for method m
     * @return the combined modifies term of the contracts in the input string, without origin
     *         labels
     * @throws SLTranslationException should not be thrown
     */
    private Term calculateCombinedModWOLabels(String contractStr) throws SLTranslationException {
        JMLSpecFactory jsf = new JMLSpecFactory(services);
        ImmutableList<TextualJMLConstruct> constructs = preParser.parseClassLevel(contractStr);

        ImmutableList<KeYJavaType> signature = ImmutableSLList.nil();
        signature = signature.append(javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT));
        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m", signature, testClassType);

        ImmutableSet<Contract> contractSet = ImmutableSet.empty();
        for (TextualJMLConstruct c : constructs) {
            if (c instanceof TextualJMLSpecCase) {
                TextualJMLSpecCase c1 = (TextualJMLSpecCase) c;
                contractSet = contractSet.union(jsf.createJMLOperationContracts(pm, c1));
            }
        }
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
        Term combinedMod = singleContract.getMod();
        return TermLabel.removeIrrelevantLabels(combinedMod, services);
    }
}
