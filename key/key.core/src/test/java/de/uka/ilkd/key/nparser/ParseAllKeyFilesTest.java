package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
@RunWith(Parameterized.class)
public class ParseAllKeyFilesTest {
    @Parameterized.Parameter
    public Path file;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        Files.walkFileTree(HelperClassForTests.TESTCASE_DIRECTORY.toPath(),
                new SimpleFileVisitor<>() {
                    @Override
                    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                        if (attrs.isRegularFile() && file.toString().endsWith(".key")) {
                            seq.add(new Object[]{file});
                        }
                        return super.visitFile(file, attrs);
                    }
                });
        return seq;
    }

    @Test
    public void parse() throws IOException {
        var ctx = ParsingFacade.parseFile(file);
        Assert.assertNull(ctx.exception);

        Services services = new Services(new JavaProfile());
        FileVisitor b = new FileVisitor(services, services.getNamespaces(), new ParsedKeyFile());
        ctx.accept(b);
    }

    public static void debugLexer(KeYLexer toks){
        Token t;
        do {
            t = toks.nextToken();
            System.out.format("%02d %20s %d:%-50s\n",
                    toks.getLine(),
                    toks.getVocabulary().getSymbolicName(t.getType()),
                    toks._mode,
                    t.getText().replace("\n", "\\n"));
            if(t.getType() == KeYLexer.ERROR_CHAR) Assert.fail();
        } while (t.getType() != CommonToken.EOF);
    }

    @Test
    public void lex() throws IOException {
        var toks = ParsingFacade.lex(file);
        debugLexer(toks);
    }
}
