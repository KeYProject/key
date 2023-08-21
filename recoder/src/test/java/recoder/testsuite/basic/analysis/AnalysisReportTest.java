/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic.analysis;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.zip.GZIPOutputStream;

import org.junit.Ignore;
import org.junit.Test;
import recoder.abstraction.ProgramModelElement;
import recoder.abstraction.Type;
import recoder.convenience.Format;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Declaration;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceElement.Position;
import recoder.java.reference.*;
import recoder.service.ConstantEvaluator.EvaluationResult;
import recoder.service.SourceInfo;
import recoder.testsuite.basic.BasicTestsSuite;
import recoder.util.HashCode;
import recoder.util.Index;
import recoder.util.Order;
import recoder.util.Sorting;

import static org.junit.Assert.fail;

@Ignore
public class AnalysisReportTest {

    final static Order UNIT_NAME_ORDER = new Order.CustomLexicalOrder() {
        protected String toString(Object x) {
            return Naming.toCanonicalName((CompilationUnit) x);
        }
    };

    /**
     * Report format:
     * <p>
     * line/column of a new position capital letters abbreviation of class name "name of compilation
     * unit" if CU :type if typed expression, either symbolic or line number of TD ==value if
     * compile-time-constant expression ->destination if reference, either symbolic or line number
     * of definition sample:
     *
     * <PRE>
     * <p>
     * 54/8 SCR ->java.lang.RuntimeException(java.lang.String) 54/14 VR
     * :java.lang.String ->112 I 11/0 CU "java.util.Dictionary" PS
     *
     * </PRE>
     * <p>
     * read: on line 54, column 8 there is a super constructor reference pointing to a runtime
     * exception constructor with argument on column 14 there is a variable reference of type String
     * and defined by the 112th element of this report at the same position there is an Identifier
     * at line 11, column 0 there is a compilation unit with logical name java.lang.dictionary (the
     * first lines are comments, obviously) at the same position there is a package specification
     * (the first "real" entry of the unit)
     */
    @Test
    public void testAnalysisReport() throws IOException {
        ByteArrayOutputStream baos = new ByteArrayOutputStream(10000);
        GZIPOutputStream gzip = new GZIPOutputStream(baos);
        OutputStreamWriter osw = new OutputStreamWriter(gzip, StandardCharsets.UTF_8);
        createReport(osw);
        osw.close();
        byte[] buffer = baos.toByteArray();
        File referenceLogFile = getLogFile();
        if (!referenceLogFile.exists()) {
            FileOutputStream fos = new FileOutputStream(referenceLogFile);
            baos.writeTo(fos);
            fos.close();
            fail("No reference log - created " + referenceLogFile.getPath());
        }
        InputStream is = new FileInputStream(referenceLogFile);
        byte[] referenceBuffer = new byte[buffer.length];
        int bsize = is.read(referenceBuffer);
        is.close();
        for (int i = buffer.length - 1; i >= 0; i -= 1) {
            if (buffer[i] != referenceBuffer[i]) {
                File failureFile = createFailureFile(referenceLogFile);
                FileOutputStream fos = new FileOutputStream(failureFile);
                baos.writeTo(fos);
                fos.close();
                fail("Reference report did not match - created protocol " + failureFile.getPath());
                break;
            }
        }
    }

    protected File getLogFile() {
        File prj = BasicTestsSuite.getProjectFile();
        String name = prj.getPath();
        if (name.endsWith(".prj") || name.endsWith(".PRJ")) {
            name = name.substring(0, name.length() - 4);
        }
        name += ".log.gz";
        return new File(name);
    }

    protected File createFailureFile(File logFile) {
        File failureFile;
        String path = logFile.getPath();
        String dir = path.substring(0, path.lastIndexOf(File.separatorChar));
        String name = path.substring(path.lastIndexOf(File.separator) + 1);
        int n = 0;
        do {
            String newName = dir + File.separator + "fail" + n + "-" + name;
            failureFile = new File(newName);
            n += 1;
        } while (failureFile.exists());
        int npidx = Math.max(0, path.lastIndexOf(File.separator));
        File newPath = new File("fail" + (n - 1) + "-" + path.substring(0, npidx));
        newPath.mkdir();
        try {
            failureFile.createNewFile();
        } catch (IOException e) {
            throw new RuntimeException("unexpected (nearly impossible) IO Error - try again");
        }
        return failureFile;
    }

    protected void createReport(Writer out) throws IOException {

        List<CompilationUnit> units =
            BasicTestsSuite.getConfig().getSourceFileRepository().getCompilationUnits();
        // sort by name
        CompilationUnit[] uarray = new CompilationUnit[units.size()];
        for (int i = 0; i < uarray.length; i++) {
            uarray[i] = units.get(i);
        }
        Sorting.heapSort(uarray, UNIT_NAME_ORDER);
        SourceInfo si = BasicTestsSuite.getConfig().getSourceInfo();
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
                // line.append(number);
                // line.append(' ');
                Position pos = pe.getFirstElement().getStartPosition();
                if (!pos.equals(oldPos)) {
                    line.append(pos);
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
                        if (BasicTestsSuite.getConfig().getConstantEvaluator()
                                .isCompileTimeConstant((Expression) pe, res)) {
                            line.append(" ==").append(res);
                        }
                    }
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
