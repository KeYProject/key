/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.key_project.rusty.parsing.RustyWhileLexer;
import org.key_project.rusty.parsing.RustyWhileParser;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class Test {
    public static void main(String[] args) {
        try {
            var example = Files.readString(Paths.get("ncore.rusty_while/examples/basic.rs"),
                Charset.defaultCharset());
            var lexer = new RustyWhileLexer(CharStreams.fromString(example));
            var ts = new CommonTokenStream(lexer);
            var parser = new RustyWhileParser(ts);
            var crate = parser.crate();
            System.out.println(crate.getText());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
