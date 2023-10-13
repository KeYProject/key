/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.util.List;

import junit.framework.Assert;
import org.junit.Test;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.convenience.Format;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.reference.*;
import recoder.service.CrossReferenceSourceInfo;
import recoder.testsuite.basic.BasicTestsSuite;

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
        for (CompilationUnit u : units) {
            TreeWalker tw = new TreeWalker(u);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if (pe instanceof Reference) {
                    Assert.assertFalse("Uncollated reference detected",
                        pe instanceof UncollatedReferenceQualifier);
                    if (pe instanceof VariableReference) {
                        VariableReference r = (VariableReference) pe;
                        Variable x = xrsi.getVariable(r);
                        List<? extends VariableReference> list = xrsi.getReferences(x);
                        if (!list.contains(r)) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    } else if (pe instanceof TypeReference) {
                        TypeReference r = (TypeReference) pe;
                        Type x = xrsi.getType(r);
                        // void type check
                        if (x != null) {
                            List<TypeReference> list = xrsi.getReferences(x);
                            if (!list.contains(r)) {
                                Assert.fail(makeReferenceError(r, x));
                            }
                        }
                    } else if (pe instanceof MethodReference) {
                        MethodReference r = (MethodReference) pe;
                        Method x = xrsi.getMethod(r);
                        List<? extends MemberReference> list = xrsi.getReferences(x);
                        if (!list.contains(r)) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    } else if (pe instanceof ConstructorReference) {
                        ConstructorReference r = (ConstructorReference) pe;
                        Constructor x = xrsi.getConstructor(r);
                        List<ConstructorReference> list = xrsi.getReferences(x);
                        if (!list.contains(r)) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    } else if (pe instanceof PackageReference) {
                        PackageReference r = (PackageReference) pe;
                        Package x = xrsi.getPackage(r);
                        List<PackageReference> list = xrsi.getReferences(x);
                        if (!list.contains(r)) {
                            Assert.fail(makeReferenceError(r, x));
                        }
                    }
                }
            }
        }
    }
}
