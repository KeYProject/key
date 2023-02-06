package recoder.testsuite.basic.analysis;

import junit.framework.Assert;
import org.junit.Test;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Format;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.reference.*;
import recoder.service.CrossReferenceSourceInfo;
import recoder.testsuite.basic.BasicTestsSuite;

import java.util.List;

/**
 * This test checks if all references in all compilation units are resolved and contained in the
 * reference lists of their corresponding target.
 */
public class ReferenceCompletenessTest {

    private static String makeReferenceError(Reference r, ProgramModelElement x) {
        return Format.toString("%c %N @%p in %f", r) + " was not found in reference list of "
            + Format.toString("%c %N", x);
    }

    @Test
    public void testReferenceCompleteness() {
        CrossReferenceSourceInfo xrsi = BasicTestsSuite.getConfig().getCrossReferenceSourceInfo();
        SourceFileRepository sfr = BasicTestsSuite.getConfig().getSourceFileRepository();

        List<CompilationUnit> units = sfr.getCompilationUnits();
        for (int i = 0; i < units.size(); i += 1) {
            CompilationUnit u = units.get(i);
            TreeWalker tw = new TreeWalker(u);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if (pe instanceof Reference) {
                    Assert.assertTrue("Uncollated reference detected",
                        !(pe instanceof UncollatedReferenceQualifier));
                    if (pe instanceof VariableReference) {
                        VariableReference r = (VariableReference) pe;
                        Variable x = xrsi.getVariable(r);
                        List<? extends VariableReference> list = xrsi.getReferences(x);
                        if (list.indexOf(r) < 0) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    } else if (pe instanceof TypeReference) {
                        TypeReference r = (TypeReference) pe;
                        Type x = xrsi.getType(r);
                        // void type check
                        if (x != null) {
                            List<TypeReference> list = xrsi.getReferences(x);
                            if (list.indexOf(r) < 0) {
                                Assert.fail(makeReferenceError(r, x));
                            }
                        }
                    } else if (pe instanceof MethodReference) {
                        MethodReference r = (MethodReference) pe;
                        Method x = xrsi.getMethod(r);
                        List<? extends MemberReference> list = xrsi.getReferences(x);
                        if (list.indexOf(r) < 0) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    } else if (pe instanceof ConstructorReference) {
                        ConstructorReference r = (ConstructorReference) pe;
                        Constructor x = xrsi.getConstructor(r);
                        List<ConstructorReference> list = xrsi.getReferences(x);
                        if (list.indexOf(r) < 0) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    } else if (pe instanceof PackageReference) {
                        PackageReference r = (PackageReference) pe;
                        Package x = xrsi.getPackage(r);
                        List<PackageReference> list = xrsi.getReferences(x);
                        if (list.indexOf(r) < 0) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    }
                }
            }
        }
    }
}
