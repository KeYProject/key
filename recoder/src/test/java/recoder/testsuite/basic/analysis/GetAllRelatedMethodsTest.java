/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.util.ArrayList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.kit.MethodKit;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.testsuite.basic.BasicTestsSuite;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

@Ignore
public class GetAllRelatedMethodsTest {
    final static String PACKAGE = "testdata.";
    CrossReferenceSourceInfo xrsi;
    NameInfo ni;

    private ClassType loadClass(String localname) {
        String name = PACKAGE + localname;
        ClassType ct = ni.getClassType(name);
        if (ct == null) {
            fail("Could not load test data " + name);
        }
        return ct;
    }

    @Test
    public void testGetAllRelatedMethodsTest() {
        this.xrsi = BasicTestsSuite.getConfig().getCrossReferenceSourceInfo();
        this.ni = BasicTestsSuite.getConfig().getNameInfo();

        // preload main class (makes the other types visible, too)
        loadClass("MethodTestData");

        ClassType ct = loadClass("Child");
        checkRelatedMethodsCount(ct, "childMethod", 1);
        checkRelatedMethodsCount(ct, "baseAndChildMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndChildAndIFirstMethod", 3);
        checkRelatedMethodsCount(ct, "baseAndIFirstMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndIFirstISecondMethod", 3);

        ct = loadClass("IFirst");
        checkRelatedMethodsCount(ct, "childAndIFirstMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndChildAndIFirstMethod", 3);
        checkRelatedMethodsCount(ct, "baseAndIFirstMethod", 2);
        // checkRelatedMethodsCount(ct, "clone",3); // Should be all classes
        // overriding clone

        ct = loadClass("Base");
        checkRelatedMethodsCount(ct, "childMethod", 0);
        checkRelatedMethodsCount(ct, "baseAndChildMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndChildAndIFirstMethod", 3);
        checkRelatedMethodsCount(ct, "baseAndIFirstMethod", 2);
    }

    private void checkRelatedMethodsCount(ClassType ct, String methodName, int expectedNumber) {
        List<Method> ml =
            MethodKit.getAllRelatedMethods(ni, xrsi, ct, methodName, new ArrayList<>(0));
        if (ml.size() != expectedNumber) {
            System.err.println("Aha");
        }
        assertEquals(methodName, expectedNumber, ml.size());
        checkSignatures(ml, methodName, new ArrayList<>(0));
    }

    private void checkSignatures(List<Method> ml, String methodName, List<Type> signature) {
        for (Method method : ml) {
            assertEquals(method.getName(), methodName);
            assertEquals(method.getSignature(), signature);
        }
    }

}
