/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSetStatement;
import de.uka.ilkd.key.speclang.jml.translation.Context;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This class holds tests for the SetStatement.
 *
 * @author Julian Wiesler
 */
public class SetStatementTest {
    /**
     * the filename of the key file which is needed to create Services and JavaInfo
     */
    private static final String TEST_FILE = HelperClassForTests.TESTCASE_DIRECTORY + File.separator
        + "setStatements" + File.separator + "testFile.key";

    /**
     * JavaInfo containing information about the available datatypes and methods
     */
    private JavaInfo javaInfo;

    /**
     * services needed for translation
     */
    private Services services;

    /**
     * service for JML translation
     */
    private JmlIO jmlIO;

    /**
     * context information needed for JmlIO/parser
     */
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
        var selfVar = new LocationVariable(new ProgramElementName("self"), testClassType);

        var normalLocal = new LocationVariable(new ProgramElementName("normalLocal"),
            javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT));
        var ghostLocal = new LocationVariable(new ProgramElementName("ghostLocal"),
            javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT), true, false);

        jmlIO = new JmlIO(services)
                .context(Context.inClass(testClassType, false, services.getTermBuilder()))
                .selfVar(selfVar)
                .parameters(
                    ImmutableSLList.<LocationVariable>nil().append(ghostLocal, normalLocal));
    }

    @Test
    public void test() {
        testError("//@ set this.ghostArray[0] = 0;", "write to array");
        testError("//@ set this.normalField = 0;", "write to normal field");
        testNoError("//@ set this.ghostArray[0].ghostField = 0;", "write ghost field");
        testNoError("//@ set this.ghostField = 0;", "write to ghost field");
        testNoError("//@ set ghostLocal = 0;", "write to ghost local");
        testError("//@ set normalLocal = 0;", "write to normal local");
    }

    private void testError(String statement, String reason) {
        assertNotNull(parseAndCheck(statement),
            "'" + statement + "' should produce an error: " + reason);
    }

    private void testNoError(String statement, String reason) {
        assertNull(parseAndCheck(statement),
            "'" + statement + "' should not produce an error: " + reason);
    }

    private String parseAndCheck(String statementText) {
        JMLSpecFactory jsf = new JMLSpecFactory(services);
        ImmutableList<TextualJMLConstruct> constructs =
            new de.uka.ilkd.key.speclang.njml.PreParser(true).parseMethodLevel(statementText, null,
                Position.newOneBased(1, 1));
        assertEquals(constructs.size(), 1);
        assertInstanceOf(TextualJMLSetStatement.class, constructs.head());
        var statement = (TextualJMLSetStatement) constructs.head();
        JmlParser.Set_statementContext context = statement.getAssignment();
        Term assignee = jmlIO.translateTerm(context.assignee);
        return jsf.checkSetStatementAssignee(assignee);
    }
}
