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
    public void testLDT() throws IOException {
        var services = new Services(new JavaProfile());
        var f = load(services, "/de/uka/ilkd/key/proof/rules/ldt.key");
        System.out.println(f);
    }

    /*
    @Test
    public void testlex() throws IOException {
        //KeYLexer lex = ParsingFacade.lex(Paths.get("C:/Users/weigl/IdeaProjects/key/key/key.core/out/production/resources/de/uka/ilkd/key/proof/rules/integerHeader.key"));
        var path = Paths.get("C:/Users/weigl/IdeaProjects/key/key/key.core/out/production/resources/de/uka/ilkd/key/proof/rules/integerHeader.key");
        KeyIO io = new KeyIO(path.toUri().toURL());
        io.loadComplete();
    }

    @Test
    public void testlex1() throws IOException {
        KeYLexer lex = ParsingFacade.lex(CharStreams.fromString("numbers 0 (numbers)"));
        ParseAllKeyFilesTest.debugLexer(lex);
    }
*/
    private ParsedKeyFile load(Services services, String resources) throws IOException {
        var url = getClass().getResource(resources);
        Assume.assumeNotNull(url, services);
        KeyIO io = new KeyIO(url, services);
        io.loadComplete();
        return null;
    }

}