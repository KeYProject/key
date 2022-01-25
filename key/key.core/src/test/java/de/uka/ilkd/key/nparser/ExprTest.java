package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class ExprTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprTest.class);

    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        InputStream s = ExprTest.class.getResourceAsStream("exprs.txt");
        Assumptions.assumeTrue(null != s);
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(s))) {
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

    @ParameterizedTest
    @CsvFileSource(resources = "exprs.txt",delimiter = '^')
    public void parseAndVisit(String expr) throws IOException {
        KeyIO io = getIo();
        Term actual = io.parseExpression(expr);
        if (actual == null) {
            DebugKeyLexer.debug(expr);
        }
        assertNotNull(actual);
        System.out.println(actual);
    }

    private KeyIO getIo() throws IOException {
        Services services = new Services(new JavaProfile());
        String p = "/de/uka/ilkd/key/proof/rules/ldt.key";
        URL url = getClass().getResource(p);
        Assumptions.assumeTrue(url != null);
        KeyIO io = new KeyIO(services);
        io.load(url).parseFile()
                .loadDeclarations()
                .loadSndDegreeDeclarations();

        NamespaceBuilder nssb = new NamespaceBuilder(services.getNamespaces());
        nssb.addVariable("aa", "int")
                .addVariable("bb", "int")
                .addVariable("cc", "int")
                .addProgramVariable("int", "x");
        return io;
    }
}