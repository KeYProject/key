/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.Namespace;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.jspecify.annotations.NonNull;

public class SchemaRustyReader extends AntlrRustyReader {
    private Namespace<@NonNull SchemaVariable> svNS;

    public SchemaRustyReader(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public void setSVNamespace(Namespace<@NonNull SchemaVariable> ns) {
        this.svNS = ns;
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
            new org.key_project.rusty.parsing.RustySchemaLexer(CharStreams.fromString(fn));
        var ts = new CommonTokenStream(lexer);
        var parser = new org.key_project.rusty.parsing.RustySchemaParser(ts);
        var converter = new SchemaConverter(svNS, getServices());
        var converted = converter.convertFunction(parser.function_());
        return new RustyBlock(converted.body());
    }
}
