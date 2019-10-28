package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Paths;

public class ParseLDTsTests {
    @Test
    public void testBoolLdt() throws IOException {
        var services = new Services(new JavaProfile());
        var f = load(services, "/de/uka/ilkd/key/proof/rules/boolean.key",
                "/de/uka/ilkd/key/proof/rules/booleanRules.key");
        System.out.println(f);
    }


    @Test
    public void testLDT() throws IOException {
        var services = new Services(new JavaProfile());
        var f = load(services, "/de/uka/ilkd/key/proof/rules/ldt.key");
        System.out.println(f);
    }

    @Test
    public void testlex() throws IOException {
        KeYLexer lex = ParsingFacade.lex(Paths.get("C:/Users/weigl/IdeaProjects/key/key/key.core/out/production/resources/de/uka/ilkd/key/proof/rules/integerHeader.key"));
        //ParseAllKeyFilesTest.debugLexer(lex);

        KeyIO io = new KeyIO();
        io.parseProblemFile(Paths.get("C:/Users/weigl/IdeaProjects/key/key/key.core/out/production/resources/de/uka/ilkd/key/proof/rules/integerHeader.key"));
    }

    @Test
    public void testlex1() throws IOException {
        KeYLexer lex = ParsingFacade.lex(CharStreams.fromString("numbers 0 (numbers)"));
        ParseAllKeyFilesTest.debugLexer(lex);
    }

    private ParsedKeyFile load(Services services, String... resources) throws IOException {
        ParsedKeyFile f = null;
        KeyIO io = new KeyIO(services);
        for (String r : resources) {
            var url = getClass().getResource(r);
            Assume.assumeNotNull(url, services);
            f = io.parseProblemFile(url);
            System.out.println(f);
        }
        Assert.assertNotNull(f);
        return f;
    }

}