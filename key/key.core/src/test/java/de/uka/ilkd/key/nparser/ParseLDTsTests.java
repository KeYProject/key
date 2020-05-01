package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.Assume;
import org.junit.Test;

import java.io.IOException;
import java.net.URL;

public class ParseLDTsTests {
    @Test
    public void testLDT() throws IOException {
        Services services = new Services(new JavaProfile());
        load(services, "/de/uka/ilkd/key/proof/rules/ldt.key");
    }

    @Test
    public void testSR() throws IOException {
        Services services = new Services(new JavaProfile());
        load(services, "/de/uka/ilkd/key/proof/rules/standardRules.key");
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
    private void load(Services services, String resources) throws IOException {
        URL url = getClass().getResource(resources);
        Assume.assumeNotNull(url, services);
        KeyIO io = new KeyIO(services);
        io.load(url).loadComplete();
    }

}