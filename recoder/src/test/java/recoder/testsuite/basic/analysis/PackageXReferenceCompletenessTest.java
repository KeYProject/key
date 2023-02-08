package recoder.testsuite.basic.analysis;

import junit.framework.Assert;
import org.junit.Test;
import recoder.abstraction.Type;
import recoder.java.reference.TypeReference;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.testsuite.basic.BasicTestsSuite;

import java.util.List;

public class PackageXReferenceCompletenessTest extends XReferenceCompletenessTest {

    @Test
    public void testPackageXReferenceCompleteness() {
        CrossReferenceSourceInfo xrsi = BasicTestsSuite.getConfig().getCrossReferenceSourceInfo();
        NameInfo ni = BasicTestsSuite.getConfig().getNameInfo();

        List<? extends Type> types = ni.getTypes();
        for (int i = 0; i < types.size(); i += 1) {
            Type x = types.get(i);
            List<TypeReference> list = xrsi.getReferences(x);
            for (int j = 0; j < list.size(); j += 1) {
                TypeReference r = list.get(j);
                Type y = xrsi.getType(r);
                if (x != y) {
                    Assert.fail(makeResolutionError(r, x, y));
                }
            }
        }
    }
}
