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
        for (int i = 0; i < classTypes.size(); i += 1) {
            ClassType t = classTypes.get(i);

            List<? extends Method> methods = t.getMethods();
            for (int j = 0; j < methods.size(); j += 1) {
                Method x = methods.get(j);
                List<? extends MemberReference> list = xrsi.getReferences(x);
                for (int k = 0; k < list.size(); k += 1) {
                    MethodReference r = (MethodReference) list.get(k);
                    Method y = xrsi.getMethod(r);
                    if (x != y) {
                        Assert.fail(makeResolutionError(r, x, y));
                    }
                }
            }

            List<? extends Constructor> constructors = t.getConstructors();
            for (int j = 0; j < constructors.size(); j += 1) {
                Constructor x = constructors.get(j);
                List<ConstructorReference> list = xrsi.getReferences(x);
                for (int k = 0; k < list.size(); k += 1) {
                    ConstructorReference r = list.get(k);
                    Constructor y = xrsi.getConstructor(r);
                    if (x != y) {
                        Assert.fail(makeResolutionError(r, x, y));
                    }
                }
            }

            List<? extends Field> fields = t.getFields();
            for (int j = 0; j < fields.size(); j += 1) {
                Field x = fields.get(j);
                List<FieldReference> list = xrsi.getReferences(x);
                for (int k = 0; k < list.size(); k += 1) {
                    FieldReference r = list.get(k);
                    Field y = xrsi.getField(r);
                    if (x != y) {
                        Assert.fail(makeResolutionError(r, x, y));
                    }
                }
            }
        }
    }
}
