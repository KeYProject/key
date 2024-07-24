/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.util.Arrays;

import org.key_project.logic.Name;
import org.key_project.rusty.ast.Converter;
import org.key_project.rusty.ast.ty.KeYRustyType;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.Semisequent;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Test;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.util.TacletForTests;

public class BasicTest {

    @Test
    public void testBasic() {
        // load
        TacletForTests.parse();
        assert TacletForTests.services().getNamespaces().programVariables()
                .lookup(new Name("i")) != null;

        var services = TacletForTests.services();
        var tb = services.getTermBuilder();

        var example = "{a = a + b;\n" +
            "b = a - b;\n" +
            "a = a - b;\n" +
            "1u32\n" +
            "}";
        var lexer =
            new org.key_project.rusty.parsing.RustyWhileLexer(CharStreams.fromString(example));
        var ts = new CommonTokenStream(lexer);
        var parser = new org.key_project.rusty.parsing.RustyWhileParser(ts);
        var block = Converter.visitBlockExpr(parser.blockExpr());

        var intSort = services.getNamespaces().sorts().lookup("int");
        var intType = new KeYRustyType(intSort);

        var a = new ProgramVariable(new Name("a"), intSort, intType);
        var b = new ProgramVariable(new Name("b"), intSort, intType);
        var a_old = new ProgramVariable(new Name("a_old"), intSort, intType);
        var b_old = new ProgramVariable(new Name("b_old"), intSort, intType);

        services.getNamespaces().programVariables()
                .add(Arrays.stream(new ProgramVariable[] { a, a_old, b, b_old }).toList());

        var mod = tb.dia(new RustyBlock(block),
            tb.and(tb.equals(tb.var(a), tb.var(b_old)), tb.equals(tb.var(b), tb.var(a_old))));
        var t = tb.imp(
            tb.and(tb.equals(tb.var(a), tb.var(a_old)), tb.equals(tb.var(b), tb.var(b_old))),
            mod); // a = a_old && b = b_old -> <example> a = b_old && b = a_old
        System.out.println(t);


        Semisequent succ = new Semisequent(new SequentFormula(t));
        Sequent s = Sequent.createSuccSequent(succ);
        Proof p = new Proof("FirstProof", TacletForTests.initConfig());
        p.setRoot(new Node(p, s));
    }

    @Test
    public void testInitialization() {

    }
}
