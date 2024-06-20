/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.key_project.rusty.ast.Converter;
import org.key_project.rusty.parsing.RustyWhileLexer;
import org.key_project.rusty.parsing.RustyWhileParser;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class Test {
    public static void main(String[] args) {
        try {
            var example = Files.readString(Paths.get("keyext.rusty_while/examples/basic.rs"),
                Charset.defaultCharset());
            var lexer = new RustyWhileLexer(CharStreams.fromString(example));
            var ts = new CommonTokenStream(lexer);
            var parser = new RustyWhileParser(ts);
            var crate = parser.crate();
            System.out.println(crate.item(0).function_().blockExpr().stmts().expr().getText());
            System.out.println(crate.getText());
            var converted = Converter.convertCrate(crate);
            System.out.println(converted);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
