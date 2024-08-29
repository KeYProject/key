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
    private final Services services;

    public RustyReader(Services services, NamespaceSet nss) {
        this.services = services;
    }

    public Services getServices() {
        return services;
    }

    /**
     * parses a given RustyBlock using the context to determine the right references
     *
     * @param block a String describing a java block
     * @param context recoder.java.CompilationUnit in which the block has to be interprested
     * @return the parsed and resolved JavaBlock
     */
    public RustyBlock readBlock(String block, Context context) {
        var fn = context.buildFunction(block);
        var lexer =
            new org.key_project.rusty.parsing.RustyLexer(CharStreams.fromString(fn));
        var ts = new CommonTokenStream(lexer);
        var parser = new org.key_project.rusty.parsing.RustyParser(ts);
        var converter = new Converter(services);
        var converted = converter.convertFunction(parser.function_());
        return new RustyBlock(converted.body());
    }

    public RustyBlock readBlockWithEmptyContext(String s) {
        return readBlock(s, createEmptyContext());
    }

    public RustyBlock readBlockWithProgramVariables(Namespace<@NonNull ProgramVariable> varNS,
            String s) {
        return readBlock(s, new Context(varNS));
    }

    /**
     * creates an empty compilation unit with a temporary name.
     *
     * @return the new recoder.java.CompilationUnit
     */
    public Context createEmptyContext() {
        return new Context(new Namespace<>());
    }
}
