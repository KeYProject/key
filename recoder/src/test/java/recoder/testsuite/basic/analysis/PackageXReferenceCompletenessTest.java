/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.util.List;

import junit.framework.Assert;
import org.junit.Test;
import recoder.abstraction.Type;
import recoder.java.reference.TypeReference;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.testsuite.basic.BasicTestsSuite;

public class PackageXReferenceCompletenessTest extends XReferenceCompletenessTest {

    @Test
    public void testPackageXReferenceCompleteness() {
        CrossReferenceSourceInfo xrsi = BasicTestsSuite.getConfig().getCrossReferenceSourceInfo();
        NameInfo ni = BasicTestsSuite.getConfig().getNameInfo();

        List<? extends Type> types = ni.getTypes();
        for (Type x : types) {
            List<TypeReference> list = xrsi.getReferences(x);
            for (TypeReference r : list) {
                Type y = xrsi.getType(r);
                if (x != y) {
                    Assert.fail(makeResolutionError(r, x, y));
                }
            }
        }
    }
}
