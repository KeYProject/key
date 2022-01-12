package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import org.junit.Assert;
import org.junit.Test;
import org.key_project.util.collection.ImmutableList;

public class TextualTranslatorTest {

    /* Testcases for issue 1667
       asserts and assumes were inserted into constructs in the wrong order
       This is a problem when they follow directly after each other
       as they got swapped when building the AST
       so the intuitive an assumption can be used in the following assert didn't work out.
     */
    @Test public void constructsOrderRightAssumeAssert() {
        String expr = "/*@assume i == 0;\n@assert i != 1;*/";
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        final ImmutableList<TextualJMLConstruct> constructs = translator.constructs;
        Assert.assertEquals(2, constructs.size());
        Assert.assertTrue(constructs.head() instanceof TextualJMLAssertStatement);
        Assert.assertEquals(TextualJMLAssertStatement.Kind.ASSUME,
                ((TextualJMLAssertStatement) constructs.head()).getKind());
        Assert.assertTrue(constructs.tail().head() instanceof TextualJMLAssertStatement);
        Assert.assertEquals(TextualJMLAssertStatement.Kind.ASSERT,
                ((TextualJMLAssertStatement) constructs.tail().head()).getKind());
    }

    @Test public void constructsOrderRightAssertAssume() {
        String expr = "//@assert i == 0;\n//@assume i != 1;";
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        final ImmutableList<TextualJMLConstruct> constructs = translator.constructs;
        Assert.assertEquals(2, constructs.size());
        Assert.assertTrue(constructs.head() instanceof TextualJMLAssertStatement);
        Assert.assertEquals(TextualJMLAssertStatement.Kind.ASSERT,
                ((TextualJMLAssertStatement) constructs.head()).getKind());
        Assert.assertTrue(constructs.tail().head() instanceof TextualJMLAssertStatement);
        Assert.assertEquals(TextualJMLAssertStatement.Kind.ASSUME,
                ((TextualJMLAssertStatement) constructs.tail().head()).getKind());
    }
}
