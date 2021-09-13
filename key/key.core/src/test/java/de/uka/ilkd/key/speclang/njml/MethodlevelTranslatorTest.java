package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;

/**
 * @author Alexander Weigl
 * @version 1 (5/15/20)
 */
@RunWith(Parameterized.class)
public class MethodlevelTranslatorTest {
    @Parameterized.Parameter(value = 0)
    public String expr = "";

    @Parameterized.Parameters()
    public static Collection<Object[]> getFiles() throws IOException {
        InputStream resourceAsStream = ExpressionTranslatorTest.class.getResourceAsStream("methodlevel.txt");
        return ClasslevelTranslatorTest.readInputs(resourceAsStream);
    }

    private Recoder2KeY r2k;
    private Services services;

    @Before
    public void setup() {
        //if (services != null) return;
        /*services = TacletForTests.services();
        r2k = new Recoder2KeY(services, services.getNamespaces());
        r2k.parseSpecialClasses();*/
    }

    @Test
    public void parseAndInterpret() throws SLTranslationException {
        Assert.assertNotEquals("", expr);
        /*KeYJavaType kjt = new KeYJavaType(Sort.ANY);
        ProgramVariable self = new LocationVariable(new ProgramElementName("self"), kjt);
        ProgramVariable result = new LocationVariable(new ProgramElementName("result"), kjt);
        ProgramVariable exc = new LocationVariable(new ProgramElementName("exc"), kjt);*/
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        try {
            JmlParser.Methodlevel_commentContext ctx = parser.methodlevel_comment();
            if (parser.getNumberOfSyntaxErrors() != 0)
                debugLexer();
        } catch (Exception e) {
            debugLexer();
        }
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
        //Translator et = new Translator(services, kjt, self, ImmutableSLList.nil(), result, exc,
        //        new HashMap<>(), new HashMap<>());
        //JmlSpecFactory factory = new JmlSpecFactory(services);
        //ContractTranslator ct = new ContractTranslator("", new Position(0,0), factory, kjt);
        //System.out.println(ctx.accept(ct));
    }

    private void debugLexer() {
        JmlLexer lexer = JmlFacade.createLexer(expr);
        DebugJmlLexer.debug(lexer);
    }
}