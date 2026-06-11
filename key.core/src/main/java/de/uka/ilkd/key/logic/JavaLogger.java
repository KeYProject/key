/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URI;
import java.nio.charset.StandardCharsets;

import de.uka.ilkd.key.java.ast.CompilationUnit;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.logic.op.ProgramMethod;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.java.StringUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (06.01.25)
 */
public class JavaLogger {
    private final static Logger log = LoggerFactory.getLogger(JavaLogger.class);
    private final static File findJavaAst;
    private final static PrintWriter out;

    static {
        try {
            findJavaAst = File.createTempFile("java_translations", ".txt");
            out = new PrintWriter(findJavaAst, StandardCharsets.UTF_8);
            log.info("Java AST matchers under: {}", findJavaAst);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static void print(String block, JavaBlock jb) {
        if (!jb.toString().equals("{}")) {
            out.format(
                "\n=== %d ======================================================\n```\n%s\n```\n\n",
                block.hashCode(), block);
            toSexpr((JavaProgramElement) jb.program(), 0, out);
            out.println();
            out.flush();
        }
    }

    private static void toSexpr(SyntaxElement s, int level, PrintWriter out) {
        if (s instanceof ProgramMethod) {
            s = ((ProgramMethod) s).getMethodDeclaration();
        }
        out.write(StringUtil.repeat(" ", level));
        out.format("%-40s : %s\n", s.getClass().getSimpleName(),
            s.toString().replace('\n', ' '));
        for (int i = 0; i < s.getChildCount(); i++) {
            toSexpr(s.getChild(i), level + 2, out);
            out.write("\n");
        }
    }

    public static void print(URI currentClassURI, CompilationUnit jb) {
        out.format(
            "\n=== %s ======================================================\n",
            currentClassURI);
        toSexpr(jb, 0, out);
        out.println();
        out.flush();
    }
}
