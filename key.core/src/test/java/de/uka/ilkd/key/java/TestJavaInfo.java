/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.File;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * This class tests several methods of the JavaInfo class
 */
public class TestJavaInfo {

    public static final String testfile = HelperClassForTests.TESTCASE_DIRECTORY + File.separator
        + "javainfo" + File.separator + "testJavaInfo.key";

    private static Services services;
    private static JavaInfo javaInfo;

    @BeforeAll
    static void setUp() {
        if (services == null || javaInfo == null) {
            HelperClassForTests helper = new HelperClassForTests();
            final ProofAggregate agg = helper.parse(new File(testfile));
            services = agg.getFirstProof().getServices();
            javaInfo = services.getJavaInfo();
        }
    }

    @AfterEach
    public void tearDown() {
    }

    @Test
    public void testRetrieveArrayTypeByJLSName() {
        assertNotNull(javaInfo.getKeYJavaType("[I"), "Did not find [I");

        assertNotNull(javaInfo.getKeYJavaType("[Ljava.lang.Object"),
            "Did not find [java.lang.Object");
    }

    @Test
    public void testRetrieveArrayTypeByAlternativeName() {
        assertNotNull(javaInfo.getKeYJavaType("int[]"), "Did not find int[]");

        assertNotNull(javaInfo.getKeYJavaType("java.lang.Object[]"),
            "Did not find java.lang.Object[]");
    }

    @Test
    public void testGetAllSubtypes() {
        assertNotNull(javaInfo.getAllSubtypes(services.getJavaInfo().getJavaLangObject()),
            "No subtypes of java.lang.Object?");
        // attention this test is not for fun, there are some methods deoending on
        // this property
        assertFalse(
            javaInfo.getAllSubtypes(services.getJavaInfo().getJavaLangObject())
                    .contains(javaInfo.getJavaLangObject()),
            "The method getAllSubtypes must not contain the type itself");
    }

    @Test
    public void testGetAllSupertypes() {
        KeYJavaType rte = javaInfo.getKeYJavaType("java.lang.RuntimeException");
        assertNotNull(rte, "Did not find class java.lang.RuntimeException");
        final ImmutableList<KeYJavaType> allSupertypes = javaInfo.getAllSupertypes(rte);

        assertNotNull(allSupertypes, "No supertypes of java.lang.RuntimeException?");

        assertTrue(allSupertypes.contains(rte),
            "The method getAllSupertypes must contain the type itself");
    }

    @Test
    public void testFindArrayLength() {
        KeYJavaType intarray = javaInfo.getKeYJavaType("int[]");
        assertNotNull(javaInfo.getAttribute("length", intarray),
            "Could not find length attribute for arrays: ");

    }

    private static final String[] implictFieldsClassOnly = new String[] {
        ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS,
        ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS,
        ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, ImplicitFieldAdder.IMPLICIT_CLASS_PREPARED };

    private static final String[] generalImplicitFields = new String[] {
        ImplicitFieldAdder.IMPLICIT_CREATED, ImplicitFieldAdder.IMPLICIT_INITIALIZED };


    @Test
    public void testFindImplicitAttributesForClassTypesOnly() {
        KeYJavaType obj = javaInfo.getKeYJavaType("java.lang.Object");
        for (String generalImplicitField : generalImplicitFields) {
            assertNotNull(javaInfo.lookupVisibleAttribute(generalImplicitField, obj),
                "Could not find " + generalImplicitField + "attribute for arrays.");
        }
        for (String anImplictFieldsClassOnly : implictFieldsClassOnly) {
            assertNotNull(javaInfo.lookupVisibleAttribute(anImplictFieldsClassOnly, obj),
                "Could not find " + anImplictFieldsClassOnly + "attribute for arrays.");
        }
    }

    /**
     * Important getAttribute methods of javaInfo must return only local declared attributes
     */
    @Test
    public void testFindAttributesLocallyDeclaredOnly() {
        KeYJavaType obj = javaInfo.getKeYJavaType("java.lang.Object");

        KeYJavaType rte = javaInfo.getKeYJavaType("java.lang.RuntimeException");


        assertNotNull(javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, obj),
            "Did not find locally declared attribute " + ImplicitFieldAdder.IMPLICIT_CREATED);

        assertNull(javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, rte),
            "Attribute " + ImplicitFieldAdder.IMPLICIT_CREATED
                + " is locally declared in class java.lang.Object and should not be "
                + "returned by this method for type java.lang.RuntimeException");

    }

    /**
     * tests if the common subtypes of two sorts are correctly determined
     */
    @Test
    public void testGetCommonSubtypes() {

        final KeYJavaType ae = javaInfo.getKeYJavaType("java.lang.ArithmeticException");
        final KeYJavaType npe = javaInfo.getKeYJavaType("java.lang.NullPointerException");

        assertEquals(0, javaInfo.getCommonSubtypes(ae, npe).size());

        final KeYJavaType obj = javaInfo.getKeYJavaType("java.lang.Object");
        final KeYJavaType rte = javaInfo.getKeYJavaType("java.lang.RuntimeException");

        long start = System.currentTimeMillis();

        final ImmutableList<KeYJavaType> commons = javaInfo.getCommonSubtypes(obj, rte);
        assertEquals(commons, javaInfo.getAllSubtypes(rte).prepend(rte));


        long end = System.currentTimeMillis();
        final long duration = end - start;

        // test caching
        long durationCache = 0;
        for (int i = 0; i < 1000; i++) {
            start = System.currentTimeMillis();
            final ImmutableList<KeYJavaType> commonsCache = javaInfo.getCommonSubtypes(obj, rte);
            end = System.currentTimeMillis();
            assertEquals(commonsCache, commons, "Cache inconsistence");
            durationCache += end - start;
        }
        assertTrue(durationCache / 1000 < duration | duration == 0 && durationCache / 1000 == 0,
            "Performance problem with caching common subsorts");


    }

    /**
     * test getPrimtiveKeYJavaType
     */
    @Test
    public void testGetPrimitiveKJT() {
        final String[] primitiveTypeNames =
            new String[] { "long", "int", "short", "byte", "char", "boolean" };

        for (String primitiveTypeName : primitiveTypeNames) {
            assertNotNull(javaInfo.getPrimitiveKeYJavaType(primitiveTypeName),
                "Type" + primitiveTypeName + " not found");
        }

        assertNull(javaInfo.getPrimitiveKeYJavaType("java.lang.Object"),
            "Ooops, non primitive type found");
        assertNull(javaInfo.getPrimitiveKeYJavaType("myOwnType"), "Ooops, non existing type found");
    }

}
