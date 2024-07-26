/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.Namespace;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.jspecify.annotations.NonNull;

public class RustyReader {
    public RustyReader(Services services, NamespaceSet nss) {
    }

    public RustyBlock readBlockWithEmptyContext(String s) {
        var lexer =
            new org.key_project.rusty.parsing.RustyWhileLexer(CharStreams.fromString(s));
        var ts = new CommonTokenStream(lexer);
        var parser = new org.key_project.rusty.parsing.RustyWhileParser(ts);
        var block = Converter.visitBlockExpr(parser.blockExpr());
        return new RustyBlock(block);
    }

    public RustyBlock readBlockWithProgramVariables(Namespace<@NonNull ProgramVariable> varNS,
            String s) {
        // TODO: Work with context
        return readBlockWithEmptyContext(s);
    }
}
