/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.java5test;

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.EventObject;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.bytecode.AnnotationUseInfo;
import recoder.bytecode.MethodInfo;
import recoder.convenience.ForestWalker;
import recoder.convenience.Format;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.io.PropertyNames;
import recoder.io.SourceFileRepository;
import recoder.java.*;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.*;
import recoder.java.reference.*;
import recoder.java.statement.EnhancedFor;
import recoder.kit.MiscKit;
import recoder.kit.transformation.java5to4.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.*;
import recoder.service.ConstantEvaluator.EvaluationResult;
import recoder.util.*;

import static org.junit.Assert.*;

/*
 * Created on 11.03.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 */

/**
 * @author gutzmann
 */
@Ignore
public class Java5Test {
    final static Order UNIT_NAME_ORDER = new Order.CustomLexicalOrder() {
        protected String toString(Object x) {
            return Naming.toCanonicalName((CompilationUnit) x);
        }
    };
    private CrossReferenceServiceConfiguration crsc;
    private SourceFileRepository dsfr;
    private final boolean silent = false;

    private void setPath(String base) {
        crsc = new CrossReferenceServiceConfiguration();
        dsfr = crsc.getSourceFileRepository();
        crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH,
            new File("test/java5/src/" + base + "/").getAbsolutePath() + File.pathSeparatorChar
                + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator
                + "jce.jar" + File.pathSeparatorChar + System.getProperty("java.home")
                + File.separatorChar + "lib" + File.separator + "jsse.jar " + File.pathSeparatorChar
                + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator
                + "rt.jar" + File.pathSeparatorChar
                + "test/java5/src/prettyprinting/testcode/java/lib/namensfehler.jar");
        crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH,
            new File("test/java5/output/" + base + "/").getAbsolutePath());
        crsc.getProjectSettings().ensureExtensionClassesAreInPath();
        crsc.getProjectSettings().ensureSystemClassesAreInPath();
    }

    private void runIt() {
        // boolean b = crsc.getProjectSettings().java5Allowed();
        crsc.getProjectSettings().setProperty(ProjectSettings.JAVA_5, "true");
        crsc.getProjectSettings().setProperty(ProjectSettings.TABSIZE, "4");
        try {
            dsfr.getAllCompilationUnitsFromPath();
            crsc.getChangeHistory().updateModel();
        } catch (ParserException pe) {
            System.err.println(pe.getMessage());
            fail("unexpected ParserException");
            // } finally {
            // crsc.getProjectSettings().setProperty(ProjectSettings.Java_5, Boolean.toString(b));
        }
        List<CompilationUnit> cul = dsfr.getCompilationUnits();
        for (CompilationUnit compilationUnit : cul) {
            compilationUnit.validateAll();
        }
    }

    private void writeBack() {
        try {
            dsfr.printAll(true);
        } catch (IOException e) {
            fail();
        }
    }

    @Test
    public void testTransformations() {
        setPath("transformations");
        // I have a copy of recoder in my test directory. Usually this directory
        // doesn't exist, though ;-)
        // setPath("recoder");
        runIt();
        List<CompilationUnit> cul = dsfr.getCompilationUnits();

        System.out.println("Starting transformations");

        /*
         * EnhancedFor2For
         */
        ForestWalker fw = new ForestWalker(cul);
        while (fw.next()) {
            ProgramElement pe = fw.getProgramElement();
            if (pe instanceof EnhancedFor) {
                EnhancedFor2For t = new EnhancedFor2For(crsc, (EnhancedFor) pe);
                t.execute();
            }
        }
        System.out.println("EnhancedFor done");

        /*
         * Var Args
         */
        cul = dsfr.getCompilationUnits();
        for (CompilationUnit value : cul) {
            new ResolveVarArgs(crsc, value).execute();
        }

        System.out.println("VarArgs done");

        /*
         * Annotations
         */
        cul = dsfr.getCompilationUnits();
        for (CompilationUnit cu : cul) {
            RemoveAnnotations t = new RemoveAnnotations(crsc, cu);
            t.execute();
        }

        System.out.println("Annotations done");

        /*
         * Static imports
         */
        cul = dsfr.getCompilationUnits();
        for (CompilationUnit unit : cul) {
            new RemoveStaticImports(crsc, unit).execute();
        }

        System.out.println("static imports done");

        /*
         * Enums
         */
        cul = dsfr.getCompilationUnits();
        for (CompilationUnit compilationUnit : cul) {
            new ReplaceEnums(crsc, compilationUnit).execute();
        }

        System.out.println("Enums done");

        /*
         * trinary operators & intersection types
         */
        cul = dsfr.getCompilationUnits();
        for (CompilationUnit cu : cul) {
            MakeConditionalCompatible t = new MakeConditionalCompatible(crsc, cu);
            t.execute();
        }

        System.out.println("Trinary operators done");

        // /*
        // * Co-variant return types DONT WORK ENTIRELY YET
        // */
        // for (int i = 0, s = cul.size(); i < s; i++) {
        // new RemoveCoVariantReturnTypes(crsc, cul.getCompilationUnit(i)).execute();
        // }
        //
        // System.out.println("Co-variant return types done");


        /*
         * now boxing
         */
        cul = dsfr.getCompilationUnits();
        for (CompilationUnit cu : cul) {
            ResolveBoxing t = new ResolveBoxing(crsc, cu);
            t.execute();
        }

        System.out.println("Boxing done");

        /*
         * Generics
         */


        // cul = dsfr.getCompilationUnits();
        // for (int i = 0; i <cul.size(); i++) {
        // new ResolveGenerics(crsc, cul.getCompilationUnit(i)).execute();
        // }

        // System.out.println("Generics done");

        writeBack();

        System.out.println("--Done--");
    }

    @Test
    public void testComments() {
        setPath("comments");
        runIt();

        ForestWalker fw = new ForestWalker(dsfr.getCompilationUnits());
        while (fw.next()) {
            ProgramElement pe = fw.getProgramElement();
            List<Comment> cl = pe.getComments();
            if (cl != null) {
                for (Comment c : cl) {
                    String name = pe.getClass().getSimpleName();
                    if (!c.getText().contains(name)) {
                        // System.err.println(pe.getClass().getName() + " - " + c.getText());
                    }
                }
            }
        }

        reparseAndCompare("comments");
    }

    @Test
    public void testAmbiguities() {
        setPath("errortest");
        final ErrorHandler defaultErrorHandler = crsc.getProjectSettings().getErrorHandler();
        defaultErrorHandler.setErrorThreshold(9999);
        crsc.getProjectSettings().setErrorHandler(new ErrorHandler() {
            private int errNum = 0;

            public int getErrorThreshold() {
                return 9999;
            }

            public void setErrorThreshold(int maxCount) {
                Debug.assertBoolean(false);
            }

            public void modelUpdating(EventObject event) { /* ignore */ }

            public void modelUpdated(EventObject event) {
                assertEquals("Not enough errors", 10, errNum);
            }

            public void reportError(Exception e) throws RuntimeException {
                switch (errNum++) {
                case 0:
                    assertTrue(e instanceof AmbiguousStaticFieldImportException);
                    break;
                case 1:
                case 2:
                case 3:
                case 4:
                case 5:
                case 6:
                case 7:
                case 8:
                case 9:
                    assertTrue(e instanceof UnresolvedReferenceException);
                    break;
                default:
                    System.err.println("failing:\n" + "    " + e.getMessage());
                    fail("Too many errors");
                }
                if (!silent) {
                    System.out.print("ok: ");
                    // taken from DefaultErrorHandler and slightly modified
                    String className = e.getClass().getName();
                    className = className.substring(className.lastIndexOf('.') + 1);
                    System.out.println("*** " + errNum + ": " + className);
                    System.out.println("    " + e.getMessage());
                    System.out.println();
                    // end of 'taken from DefaultErrorHandler'
                }
            }
        });
        runIt();

        // reparseAndCompare("errortest"); would cause too many errors
    }

    private String getAnnotationName(AnnotationUse au) {
        if (au instanceof AnnotationUseInfo) {
            AnnotationUseInfo aus = (AnnotationUseInfo) au;
            return dsfr.getServiceConfiguration().getByteCodeInfo().getAnnotationType(aus)
                    .getFullName();
        } else {
            AnnotationUseSpecification aus = (AnnotationUseSpecification) au;
            return dsfr.getServiceConfiguration().getSourceInfo().getAnnotationType(aus)
                    .getFullName();
        }
    }

    @Test
    public void testAnnotations() {
        setPath("annotationtest");
        runIt();
        // test source code annotation support
        NameInfo ni = dsfr.getServiceConfiguration().getNameInfo();
        Package p = ni.getPackage("annotationtest");
        List<? extends AnnotationUse> ann = p.getPackageAnnotations();
        assertEquals(1, ann.size());
        ByteCodeInfo bi = dsfr.getServiceConfiguration().getByteCodeInfo();
        assertEquals("annotationtest.Annot", getAnnotationName(ann.get(0)));

        p = ni.getPackage("a");
        ann = p.getPackageAnnotations();
        assertEquals(1, ann.size());
        assertEquals("a.B", getAnnotationName(ann.get(0)));
        assertNull(ni.getType("annotationtest.package-info"));
        assertNull(ni.getType("a.package-info"));

        // test bytecode annotation support
        ClassType ct = ni.getClassType("java.lang.annotation.Retention");
        assertNotNull(ct);
        assertTrue(ct.isAnnotationType());
        assertEquals(3, ct.getAllSupertypes().size());

        ct = ni.getClassType("a.C");
        List<? extends Method> ml = ct.getMethods();
        for (Method method : ml) {
            MethodInfo m = (MethodInfo) method;
            String[] param = m.getParameterTypeNames();

            System.out.print(m.getName() + "(");
            boolean first = true;
            for (int j = 0; j < param.length; j++) {
                if (!first) {
                    System.out.print(",");
                }
                first = false;
                AnnotationUseInfo[] annot = m.getAnnotationsForParam(j);
                for (AnnotationUseInfo annotationUseInfo : annot) {
                    System.out.print(annotationUseInfo + " ");
                }
                System.out.print(param[j]);
            }
            System.out.println(")");
        }
        System.out.println(ni.getClassType("a.BC").getAllMethods().size());

        reparseAndCompare("annotationtest");
    }

    @Test
    public void testEnums() {
        setPath("enumtest");
        runIt();
        NameInfo ni = dsfr.getServiceConfiguration().getNameInfo();
        EnumDeclaration etd = (EnumDeclaration) ni.getType("enumtest.Color");
        Constructor c = etd.getConstructors().get(0);
        List<ConstructorReference> crl = crsc.getCrossReferenceSourceInfo().getReferences(c);
        assertEquals(3, crl.size());

        EnumConstantSpecification ecd =
            (EnumConstantSpecification) ni.getField("enumtest.jls.Operation.PLUS");
        Method m = ecd.getConstructorReference().getClassDeclaration().getMethods().get(0);
        int s = crsc.getCrossReferenceSourceInfo().getReferences(m).size();
        // assertTrue(s == 1);
        reparseAndCompare("enumtest");
    }

    @Test
    public void testGenerics() {
        setPath("generictest");
        runIt();
        crsc.getNameInfo().getType("a.BytecodeGenerics");

        NameInfo ni = dsfr.getServiceConfiguration().getNameInfo();
        TypeDeclaration td = (TypeDeclaration) ni.getType("generictest.D");
        for (int i = 0; i < td.getMethods().size(); i++) {
            Method m = td.getMethods().get(i);
            if (m.getName().equals("foobar")) {
                MethodDeclaration md = (MethodDeclaration) m;
                assertEquals("List<List<Map<String, List<String>>>>",
                    md.getTypeReference().toSource().trim());
                // TreeWalker tw = new TreeWalker(md);
                // while (tw.next()) {
                // ProgramElement pe = tw.getProgramElement();
                // System.out.println(pe.getClass().getName() + " " + pe.getStartPosition());
                // }
            }
        }
        // System.err.println(td.toSource());
        reparseAndCompare("generictest");
    }

    private void reparseAndCompare(String path) {
        try {
            StringWriter oldReport = new StringWriter(10000);
            createExtendedReport(oldReport);
            scrubOutputPath("test/java5/output/" + path + "/");
            writeBack();
            setPath("../output/" + path + "/");
            runIt();
            StringWriter newReport = new StringWriter(10000);
            createExtendedReport(newReport);
            StringBuffer oldBuf = oldReport.getBuffer();
            StringBuffer newBuf = newReport.getBuffer();
            // assertTrue(oldBuf.length() == newBuf.length());

            for (int i = 0, rep = 5; i < Math.min(oldBuf.length(), newBuf.length())
                    && rep > 0; i++) {
                if (oldBuf.charAt(i) != newBuf.charAt(i)) {
                    if (i > 1 && oldBuf.charAt(i - 1) == '.') {
                        // may be an anonymous class: skip till next '.', but at most 10(?) digits.
                        // TODO deal with numbers of different length...
                        int j = i + 1;
                        while (Character.isDigit(oldBuf.charAt(j))
                                && Character.isDigit(newBuf.charAt(j)) && j < i + 10) {
                            j++;
                        }
                        if (j - i > 6) {
                            i = j;
                        }
                        continue;
                    }
                    // System.err.println(i);
                    // System.err.println(oldBuf.substring(i-10, i+10));
                    // System.err.println(newBuf.substring(i-10, i+10));
                    // System.err.println();
                    rep--;
                }
            }
        } catch (IOException e) {
            fail();
        }
    }

    private void scrubOutputPath(String path) {
        File myPath = new File(path);
        File[] list = myPath.listFiles();
        if (list == null) {
            return;
        }
        for (File current : list) {
            if (current.isDirectory()) {
                scrubOutputPath(current.getAbsolutePath());
                current.delete(); // if possible...
            } else if (current.isFile() && current.getName().endsWith(".java")) {
                current.delete();
            }
        }
    }

    @Test
    public void testPrettyPrinter() {
        setPath("prettyprinting");
        runIt();
        ClassDeclaration cd = (ClassDeclaration) crsc.getNameInfo().getClassType("A");
        List<? extends Field> fl = cd.getFields();
        ASTList<Comment> cml = new ASTArrayList<>(1);
        cml.add(new Comment("/*comment to field spec 'a'*/", true));
        ((FieldSpecification) fl.get(0)).setComments(cml);
        MiscKit.unindent((FieldSpecification) fl.get(0));
        // System.err.println(((FieldSpecification)fl.getField(0)).toSource());
        // System.err.println(cd.getMembers().getMemberDeclaration(0).toSource());
        // System.err.println(cd.getMembers().getMemberDeclaration(1).toSource());
        // System.err.println(((FieldSpecification)fl.getField(1)).toSource());
        //
        // //System.err.println()
        //
        // for (int i = 0; i <
        // crsc.getCrossReferenceSourceInfo().getReferences(crsc.getNameInfo().getClassType("listexample.NTuple").getConstructors().getConstructor(0)).size();
        // i++) {
        // ConstructorReference cr =
        // crsc.getCrossReferenceSourceInfo().getReferences(crsc.getNameInfo().getClassType("listexample.NTuple").getConstructors().getConstructor(0)).getConstructorReference(i);
        // System.err.println(cr.toSource());
        // }

        reparseAndCompare("prettyprinting");
    }

    protected void createExtendedReport(Writer out) throws IOException {
        List<CompilationUnit> units = crsc.getSourceFileRepository().getCompilationUnits();
        // sort by name
        CompilationUnit[] uarray = new CompilationUnit[units.size()];
        for (int i = 0; i < uarray.length; i++) {
            uarray[i] = units.get(i);
        }
        Sorting.heapSort(uarray, UNIT_NAME_ORDER);
        SourceInfo si = crsc.getSourceInfo();
        Index decl2num = new Index(HashCode.IDENTITY);
        EvaluationResult res = new EvaluationResult();
        for (int i = 0, n = 0; i < uarray.length; i += 1) {
            TreeWalker tw = new TreeWalker(uarray[i]);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if (pe instanceof Declaration) {
                    decl2num.put(pe, n);
                }
                n += 1;
            }
        }
        StringBuilder line = new StringBuilder(1024);
        int number = 1;
        for (CompilationUnit unit : uarray) {
            TreeWalker tw = new TreeWalker(unit);
            Position oldPos = Position.UNDEFINED;
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                line.append("(").append(pe.getComments() == null ? 0 : pe.getComments().size())
                        .append(" comments)");
                // line.append(number);
                // line.append(' ');
                Position pos = pe.getFirstElement().getStartPosition();
                if (!pos.equals(oldPos)) {
                    // line.append(pos); // we're not really interested in exact positions
                    oldPos = pos;
                }
                line.append(' ');
                String name = pe.getClass().getName();
                name = name.substring(name.lastIndexOf('.') + 1);
                for (int k = 0, s = name.length(); k < s; k += 1) {
                    char c = name.charAt(k);
                    if (Character.isUpperCase(c)) {
                        line.append(c);
                    }
                }
                if (pe instanceof CompilationUnit) {
                    line.append(Format.toString(" \"%u\"", pe));
                }
                if (pe instanceof Expression) {
                    Type t = si.getType(pe);
                    if (t != null) {
                        line.append(" :");
                        if (t instanceof ProgramElement) {
                            line.append(decl2num.get(t));
                        } else {
                            line.append(Format.toString("%N", t));
                        }
                        if (crsc.getConstantEvaluator().isCompileTimeConstant((Expression) pe,
                            res)) {
                            line.append(" ==").append(res);
                        }
                    }
                }
                int ref = -1;
                if (pe instanceof Constructor) {
                    ref = crsc.getCrossReferenceSourceInfo().getReferences((Constructor) pe).size();
                }
                if (pe instanceof Field) {
                    ref = crsc.getCrossReferenceSourceInfo().getReferences((Field) pe).size();
                }
                if (pe instanceof Method) {
                    ref = crsc.getCrossReferenceSourceInfo().getReferences((Method) pe).size();
                }
                if (pe instanceof Type) {
                    ref = crsc.getCrossReferenceSourceInfo().getReferences((Type) pe).size();
                }
                if (pe instanceof Variable) {
                    ref = crsc.getCrossReferenceSourceInfo().getReferences((Variable) pe).size();
                }
                if (ref != -1) {
                    line.append("(").append(ref).append(" refs)");
                }

                ProgramModelElement dest = null;
                if (pe instanceof ConstructorReference) {
                    dest = si.getConstructor((ConstructorReference) pe);
                } else if (pe instanceof MethodReference) {
                    dest = si.getMethod((MethodReference) pe);
                } else if (pe instanceof VariableReference) {
                    dest = si.getVariable((VariableReference) pe);
                } else if (pe instanceof TypeReference) {
                    dest = si.getType((TypeReference) pe);
                } else if (pe instanceof PackageReference) {
                    dest = si.getPackage((PackageReference) pe);
                }
                if (dest != null) {
                    line.append(" ->");
                    if (dest instanceof ProgramElement) {
                        line.append(decl2num.get(dest));
                    } else {
                        line.append(Format.toString("%N", dest));
                    }
                }
                line.append("\n");
                out.write(line.toString());
                line.setLength(0);
                number += 1;
            }
        }
        out.flush();
    }

}
