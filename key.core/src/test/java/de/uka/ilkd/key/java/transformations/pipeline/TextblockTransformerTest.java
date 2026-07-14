/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.io.IOException;
import java.io.InputStream;

import org.key_project.util.java.IOUtil;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.google.common.truth.Truth;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.fail;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/31/26)
 */
class TextblockTransformerTest {
    @Test
    void transform() throws IOException {
        final InputStream expected = getClass().getResourceAsStream("Textblock.expected.java");
        final InputStream input = getClass().getResourceAsStream("Textblock.java");
        assertNotNull(input);
        assertNotNull(expected);

        JavaParser parser = new JavaParser();
        parser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.RAW);

        ParseResult<CompilationUnit> result = parser.parse(input);
        if (!result.isSuccessful()) {
            result.getProblems().forEach(System.err::println);
            fail("Parsing of fixture failed.");
        }


        CompilationUnit cu = result.getResult().get();

        TextblockTransformer transformer = new TextblockTransformer();
        transformer.apply(cu);

        String expectedJava = IOUtil.readFrom(expected);
        Truth.assertThat(cu.toString()).isEqualTo(expectedJava);
    }
}
