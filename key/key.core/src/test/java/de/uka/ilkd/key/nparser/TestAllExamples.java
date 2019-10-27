package de.uka.ilkd.key.nparser;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.io.IOException;
import java.net.URL;
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
public class TestAllExamples {
    @Parameterized.Parameter
    public Path file;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        File examples = FindResources.findFolder("key.ui/examples", "../key.ui/examples");
        Assume.assumeTrue(examples != null);
        Files.walkFileTree(examples.toPath(),
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
        KeyIO io = getIo();
        ParsedKeyFile pkf = io.parseProblemFile(file);
        System.out.println(pkf);
        Assert.assertTrue(pkf.problemTerm != null || pkf.getChooseContract() != null || pkf.getProofObligation() != null);
    }

    private KeyIO getIo() throws IOException {
        KeyIO io = new KeyIO();
        URL u = getClass().getResource("/de/uka/ilkd/key/proof/rules/ldt.key");
        ParsedKeyFile pkf = io.parseProblemFile(u);
        return io;
    }
}

