package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (5/15/20)
 */
@RunWith(Parameterized.class)
public class ClasslevelTranslatorTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ClasslevelTranslatorTest.class);

    @Parameterized.Parameter()
    public String expr = "";

    @Parameterized.Parameters()
    public static Collection<Object[]> getFiles() throws IOException {
        InputStream resourceAsStream = ExpressionTranslatorTest.class.getResourceAsStream("classlevel.txt");
        return readInputs(resourceAsStream);
    }

    static Collection<Object[]> readInputs(InputStream resourceAsStream) throws IOException {
        List<Object[]> seq = new LinkedList<>();
        try (InputStream s = resourceAsStream;
             BufferedReader reader = new BufferedReader(new InputStreamReader(s))) {
            String l;
            StringBuilder content = new StringBuilder();
            while ((l = reader.readLine()) != null) {
                if (l.trim().isEmpty() || l.startsWith("#"))
                    continue;
                content.append(l).append('\n');
            }
            final String[] split = content.toString().split("---\\s*Contract\\s*---\n");
            LOGGER.debug("cases: {}", split.length);
            for (String value : split) {
                value = value.trim();
                if (!value.isEmpty())
                    seq.add(new Object[]{value.replaceAll("---Contract---", "")});
            }
        }
        return seq;
    }


    @Before
    public void setup() {}

    @Test
    public void parseAndInterpret() {
        Assert.assertNotEquals("", expr);
        KeYJavaType kjt = new KeYJavaType(Sort.ANY);
        ProgramVariable self = new LocationVariable(new ProgramElementName("self"), kjt);
        ProgramVariable result = new LocationVariable(new ProgramElementName("result"), kjt);
        ProgramVariable exc = new LocationVariable(new ProgramElementName("exc"), kjt);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.Classlevel_commentsContext ctx = parser.classlevel_comments();
        if (parser.getNumberOfSyntaxErrors() != 0) {
            System.out.println(expr);
            debugLexer();
        }
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
    }

    private void debugLexer() {
        JmlLexer lexer = JmlFacade.createLexer(expr);
        DebugJmlLexer.debug(lexer);
    }
}