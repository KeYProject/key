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

public class SchemaRustyReader extends RustyReader {
    private Namespace<@NonNull SchemaVariable> svNS;

    public SchemaRustyReader(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public void setSVNamespace(Namespace<@NonNull SchemaVariable> ns) {
        this.svNS = ns;
    }

    public RustyBlock readBlockWithEmptyContext(String s) {
        var lexer =
            new org.key_project.rusty.parsing.RustyWhileSchemaLexer(CharStreams.fromString(s));
        var ts = new CommonTokenStream(lexer);
        var parser = new org.key_project.rusty.parsing.RustyWhileSchemaParser(ts);
        var converter = new SchemaConverter(svNS, getServices());
        var block = converter.convertBlockExpr(parser.blockExpr());
        return new RustyBlock(block);
    }
}
