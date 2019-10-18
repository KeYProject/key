package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
@RunWith(Parameterized.class)
public class ExprTest {
    @Parameterized.Parameter
    public String expr;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        try (InputStream s = ExprTest.class.getResourceAsStream("exprs.txt");
             BufferedReader reader = new BufferedReader(new InputStreamReader(s))) {
            String l;
            while ((l = reader.readLine()) != null) {
                if (l.isBlank() || l.startsWith("#")) {
                    continue;
                }
                seq.add(new Object[]{l});
            }
        }
        return seq;
    }

    @Test
    public void parseAndVisit() {
        KeyIO io = getIo();
        var actual = io.parseExpression(expr);
        if(actual==null){
            ParseAllKeyFilesTest.debugLexer(ParsingFacade.lex(CharStreams.fromString(expr)));
        }
        Assert.assertNotNull(actual);
        System.out.println(actual);
    }

    private KeyIO getIo() {
        Services services = new Services(new JavaProfile());
        NamespaceSet nss = services.getNamespaces();
        NamespaceBuilder nssb = new NamespaceBuilder(nss);
        nssb.addSort("numbers").addSort("int");
        for (int i = 0; i < 9; i++) {
            nssb.addFunction("numbers "+i+"(numbers)");
        }
        nssb.addFunction("numbers #()")
                .addFunction("int Z(numbers)")
                .addFunction("numbers neglit(numbers)")
                .addFunction("int add(int, int)")
                .addFunction("int neg(int)")
                .addFunction("int sub(int, int)")
                .addFunction("int mul(int, int)")
                .addFunction("int div(int, int)")
                .addFunction("int mod(int, int)")
                .addFunction("int pow(int, int)");
        nssb.addPredicate("leq(int, int)")
                .addPredicate("lt(int, int)")
                .addPredicate("geq(int, int)")
                .addPredicate("gt(int, int)");
        ;

        nssb.addVariable("aa", "int")
                .addVariable("bb", "int")
                .addVariable("cc", "int");

        KeyIO io = new KeyIO(services, nss);
        return io;
    }
}