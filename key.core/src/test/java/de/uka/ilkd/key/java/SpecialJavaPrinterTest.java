/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests that {@link SpecialJavaPrinter} reproduces JML comments verbatim instead of wrapping the
 * already complete comment text in another JML comment marker.
 */
class SpecialJavaPrinterTest {
    private static String print(String javaCode) {
        var configuration = new ParserConfiguration();
        configuration.setStoreTokens(true);
        var result = new JavaParser(configuration).parse(javaCode);
        assertThat(result.isSuccessful()).isTrue();

        CompilationUnit unit = result.getResult().orElseThrow();
        Printer printer = new DefaultPrettyPrinter(SpecialJavaPrinter::new,
            new DefaultPrinterConfiguration());
        return printer.print(unit);
    }

    @Test
    void printsTypeLevelBlockCommentOnce() {
        String printed = print("""
                /*@ nullable */
                class Example {
                }
                """);

        assertThat(printed).contains("/*@ nullable */");
        assertThat(printed).doesNotContain("//@ /*@");
        assertThat(printed).doesNotContain("//@ //@");
    }

    @Test
    void printsLineCommentOnce() {
        String printed = print("""
                class Example {
                    //@ requires true;
                    void m() {
                    }
                }
                """);

        assertThat(printed).contains("//@ requires true;");
        assertThat(printed).doesNotContain("//@ /*@");
        assertThat(printed).doesNotContain("//@ //@");
    }
}
