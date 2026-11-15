/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.speclang.PositionedString;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the JML parser facade, in particular the position propagation from JMLtk AST nodes
 * into the re-parsed text.
 */
class JmlFacadeTest {

    @Test
    void positionedStringPreservesSourceAndLine(@TempDir Path tempDir) throws Exception {
        Path source = tempDir.resolve("Foo.java");
        Files.writeString(source, """
                class Foo {
                    int field;
                    /*@ normal_behavior
                      @ ensures field == 21;
                      @*/
                    void m() {
                    }
                }
                """);

        CompilationUnit cu = new JavaParser(new ParserConfiguration().setProcessJml(true))
                .parse(source)
                .getResult()
                .orElseThrow();
        JmlContract contract = cu.findFirst(JmlContract.class).orElseThrow();
        JmlClause clause = contract.getClauses().get(0);

        PositionedString positioned = JmlFacade.positionedString(clause, "ensures field == 21;");

        assertThat(positioned.getLocation().getFileUri()).isEqualTo(source.toUri());
        assertThat(positioned.getLocation().getPosition().line()).isEqualTo(4);
    }
}
