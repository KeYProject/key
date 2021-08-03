package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.collection.ImmutableSLList;

import java.io.*;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (5/14/20)
 */
@RunWith(Parameterized.class)
public class ExpressionTranslatorTest {
    @Parameterized.Parameter
    public String expr;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        try (InputStream s = ExpressionTranslatorTest.class.getResourceAsStream("exprs.txt");
             BufferedReader reader = new BufferedReader(new InputStreamReader(s))) {
            String l;
            while ((l = reader.readLine()) != null) {
                if (l.trim().isEmpty() || l.startsWith("#")) {
                    continue;
                }
                seq.add(new Object[]{l});
            }
        }
        return seq;
    }

    private Recoder2KeY r2k;
    private Services services;

    @Before
    public void setup() {
        if (services != null) return;
        services = TacletForTests.services();
        r2k = new Recoder2KeY(services, services.getNamespaces());
        r2k.parseSpecialClasses();
    }

    @Test
    public void parseAndInterpret() {
        KeYJavaType kjt = new KeYJavaType(Sort.ANY);
        LocationVariable self = new LocationVariable(new ProgramElementName("self"), kjt);
        LocationVariable result = new LocationVariable(new ProgramElementName("result"), kjt);
        LocationVariable exc = new LocationVariable(new ProgramElementName("exc"), kjt);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        lexer._mode = JmlLexer.expr;
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.ExpressionContext ctx = parser.expression();
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
        Translator et = new Translator(services, kjt, self, ImmutableSLList.nil(), result, exc,
                new HashMap<>(), new HashMap<>());
        System.out.println(ctx.accept(et));
    }
}