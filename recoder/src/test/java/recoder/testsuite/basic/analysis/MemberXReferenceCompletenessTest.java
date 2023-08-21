/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.util.List;

import junit.framework.Assert;
import org.junit.Test;
import recoder.abstraction.ClassType;
import recoder.abstraction.Constructor;
import recoder.abstraction.Field;
import recoder.abstraction.Method;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.testsuite.basic.BasicTestsSuite;

public class MemberXReferenceCompletenessTest extends XReferenceCompletenessTest {

    @Test
    public void testMemberXReferenceCompletenessTest() {
        CrossReferenceSourceInfo xrsi = BasicTestsSuite.getConfig().getCrossReferenceSourceInfo();
        NameInfo ni = BasicTestsSuite.getConfig().getNameInfo();

        List<? extends ClassType> classTypes = ni.getClassTypes();
        for (ClassType t : classTypes) {
            List<? extends Method> methods = t.getMethods();
            for (Method x : methods) {
                List<? extends MemberReference> list = xrsi.getReferences(x);
                for (MemberReference memberReference : list) {
                    MethodReference r = (MethodReference) memberReference;
                    Method y = xrsi.getMethod(r);
                    if (x != y) {
                        Assert.fail(makeResolutionError(r, x, y));
                    }
                }
            }

            List<? extends Constructor> constructors = t.getConstructors();
            for (Constructor x : constructors) {
                List<ConstructorReference> list = xrsi.getReferences(x);
                for (ConstructorReference r : list) {
                    Constructor y = xrsi.getConstructor(r);
                    if (x != y) {
                        Assert.fail(makeResolutionError(r, x, y));
                    }
                }
            }

            List<? extends Field> fields = t.getFields();
            for (Field x : fields) {
                List<FieldReference> list = xrsi.getReferences(x);
                for (FieldReference r : list) {
                    Field y = xrsi.getField(r);
                    if (x != y) {
                        Assert.fail(makeResolutionError(r, x, y));
                    }
                }
            }
        }
    }
}
