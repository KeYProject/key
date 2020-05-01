package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.nparser.builder.ProblemFinder;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.helper.FindResources;
import org.key_project.util.testcategories.Interactive;

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
@Category(Interactive.class)
@Ignore
public class TestAllExamples {
    @Parameterized.Parameter
    public Path file;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        try {
            Thread.sleep(10000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        List<Object[]> seq = new LinkedList<>();
        File examples = FindResources.findFolder("key.ui/examples", "../key.ui/examples");
        Assume.assumeTrue(examples != null);
        Files.walkFileTree(examples.toPath(),
                new SimpleFileVisitor<Path>() {
                    @Override
                    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
                        if (attrs.isRegularFile() && file.toString().endsWith(".key")
                            //&& file.toString().contains("Agatha")
                        ) {
                            seq.add(new Object[]{file});
                        }
                        return super.visitFile(file, attrs);
                    }
                });
        return seq;//return seq.subList(0,50);
    }

    @Test
    @Ignore("Not all files are parseable without Java Type support. ")
    public void parse() throws IOException {
        KeyIO io = getIo();
        ProblemFinder o = io.load(file).loadCompleteProblem();
        System.out.println(o);
        //Assert.assertTrue(pkf.problemTerm != null || pkf.getChooseContract() != null || pkf.getProofObligation() != null);
    }

    private KeyIO getIo() throws IOException {
        URL u = getClass().getResource("/de/uka/ilkd/key/proof/rules/standardRules.key");
        KeyIO io = new KeyIO();
        io.load(u).loadComplete();
        io.getServices().getTypeConverter().init();
        return io;
    }
}

