package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
@RunWith(Parameterized.class)
public class ExprTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprTest.class);

    @Parameterized.Parameter
    public String expr;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        InputStream s = ExprTest.class.getResourceAsStream("exprs.txt");
        Assume.assumeNotNull(s);
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

    @Test
    public void parseAndVisit() throws IOException {
        KeyIO io = getIo();
        @Nonnull Term actual = io.parseExpression(expr);
        Assert.assertNotNull(actual);
        LOGGER.info("Actual Term: {}", actual);

        LOGGER.warn("Actual Term: {}",
                LogicPrinter.quickPrintTerm(actual, io.getServices(), true, true));
    }

    private KeyIO getIo() throws IOException {
        Services services = new Services(new JavaProfile());

        String p = "/de/uka/ilkd/key/proof/rules/ldt.key";
        URL url = getClass().getResource(p);
        Assume.assumeNotNull(url);
        KeyIO io = new KeyIO(services);
        io.load(url).parseFile()
                .loadDeclarations()
                .loadSndDegreeDeclarations();

        NamespaceBuilder nssb = new NamespaceBuilder(services.getNamespaces());
        nssb.addVariable("aa", "int")
                .addVariable("bb", "int")
                .addVariable("cc", "int")
                .addProgramVariable("int", "x");

        // Without this call, the LDTs are not available to the expression
        // builder. Probably a problem of the mocking here. (MU)
        services.getTypeConverter().init();

        return io;
    }
}