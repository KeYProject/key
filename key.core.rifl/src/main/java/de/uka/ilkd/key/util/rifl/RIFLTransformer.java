/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.rifl;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection.Walker;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.MethodDeclaration;

import static org.key_project.util.Strings.*;

/**
 * Facet class for interpreting RIFL specifications. The Requirements for Information Flow Language
 * (RIFL) is a tool-independent specification language developed in the RS3 project. Method
 * <code>transform</code> reads a RIFL file and Java sources and writes JML* information flow
 * specifications to the original Java files.
 * <p>
 * <b>changes (weigl, 2016-08-16):</b> changed interfaces to File. This avoid some crud string
 * operations on filenames
 *
 * @author bruns
 * @author weigl, 2016-08-17
 */
public class RIFLTransformer {
    private static final Logger LOGGER = LoggerFactory.getLogger(RIFLTransformer.class);

    private final List<Path> result = new ArrayList<>();

    public RIFLTransformer() throws ParserConfigurationException, SAXException {
        JPF.initialize(new CrossReferenceServiceConfiguration());
        assert JPF.getServiceConfiguration() != null;
    }


    private static final JavaProgramFactory JPF =
        de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory.getInstance();

    /**
     * Entry point for the stand-alone RIFL to JML* tool.
     */
    public static void main(String[] args) {
        if (args.length < 2 || "--help".equals(args[0])) {
            LOGGER.info("This is the RIFL to JML* transformer.");
            LOGGER.info("Usage: <RIFL file> <Java sources>");
        } else {
            final File riflFilename = new File(args[0]);
            final File javaFilename = new File(args[1]);
            transform(riflFilename.toPath(), javaFilename.toPath());
        }
    }

    /**
     * Transforms plain Java files + RIFL specification to Java+JML* specifications.
     *
     * @param riflFilename path to a RIFL file
     * @param javaSource path to Java sources (should be a directory)
     * @param savePath custom save path
     * @param kexh
     */
    public static boolean transform(Path riflFilename, Path javaSource, Path savePath,
            KeYRecoderExcHandler kexh) {
        if (riflFilename == null || javaSource == null || savePath == null || kexh == null) {
            throw new IllegalArgumentException("A parameter is null");
        }

        RIFLTransformer rt;
        try {
            rt = new RIFLTransformer();
            rt.doTransform(riflFilename, javaSource, savePath);
            return true;
        } catch (final ParserConfigurationException | SAXException | ParserException
                | IOException e) {
            kexh.reportException(e);
        }
        return false;
    }

    public static boolean transform(Path riflFilename, Path javaSource, KeYRecoderExcHandler kexh) {
        return transform(riflFilename, javaSource, getDefaultSavePath(javaSource), kexh);
    }

    public static boolean transform(Path riflFilename, Path javaSource) {
        return transform(riflFilename, javaSource, SimpleRIFLExceptionHandler.INSTANCE);
    }

    /**
     * Returns the default save path for transformed Java files.
     *
     * @param origSourcePath path to a directory or single Java file
     * @return path to the transformed directory
     */
    public static Path getDefaultSavePath(Path origSourcePath) {
        // TODO weigl: Shouldn't we use the old directory, because of reference to other java files?
        origSourcePath = getBaseDirPath(origSourcePath);
        return origSourcePath.resolveSibling(origSourcePath.getFileName() + "_RIFL");
    }

    private static Path getBaseDirPath(Path origSourcePath) {
        if (Files.isRegularFile(origSourcePath)) {
            return origSourcePath.getParent();
        } else {
            return origSourcePath;
        }
    }

    private Map<CompilationUnit, Path> readJava(Path root) throws IOException, ParserException {
        assert Files.exists(root) : "source dir must exist";
        assert Files.isDirectory(root) : "source must be directory";
        final DirectoryFileCollection files = new DirectoryFileCollection(root);
        final Walker walker = files.createWalker(".java");

        final ServiceConfiguration serviceConfiguration = JPF.getServiceConfiguration();
        Map<CompilationUnit, Path> javaCUs = new HashMap<>();

        // parse
        while (walker.step()) {
            final Path javaFile = Paths.get(walker.getCurrentName());
            // debug
            if (Debug.ENABLE_DEBUG) {
                LOGGER.info("[RIFL] Read file: {}", javaFile);
            }

            final CompilationUnit cu;

            try (Reader fr = Files.newBufferedReader(javaFile, StandardCharsets.UTF_8)) {
                cu = JPF.parseCompilationUnit(fr);

                // crud relative
                Path relative = relative(root, javaFile);
                javaCUs.put(cu, relative); // relative path
                serviceConfiguration.getChangeHistory().updateModel(); // workaround to an issue in
                // recoder
            }
        }
        return javaCUs;
    }

    private Path relative(Path root, Path javaFile) {
        return javaFile.relativize(root);
    }

    private SpecificationContainer readRIFL(Path fileName)
            throws IOException, SAXException, ParserConfigurationException {
        // TODO: validate input file
        final SAXParserFactory spf = SAXParserFactory.newInstance();
        spf.setFeature("http://xml.org/sax/features/external-general-entities", false);
        spf.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
        spf.setNamespaceAware(true);

        SAXParser saxParser = spf.newSAXParser();
        XMLReader xmlReader = saxParser.getXMLReader();
        // xmlReader.setFeature("http://xml.org/sax/features/validation", true);
        xmlReader.setContentHandler(new RIFLHandler());
        xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
        xmlReader.parse(fileName.toUri().toString());
        return ((RIFLHandler) xmlReader.getContentHandler()).getSpecification();
    }

    public void doTransform(final Path riflFilename, final Path source, final Path savePath)
            throws IOException, SAXException, ParserException, ParserConfigurationException {
        ensureTargetDirExists(savePath);
        final Path javaRoot = getBaseDirPath(source);

        // step 1: read files
        SpecificationContainer sc = readRIFL(riflFilename);
        Map<CompilationUnit, Path> javaCUs = readJava(javaRoot);
        int counter = 0;
        // step 2: inject specifications
        // TODO rename the public class in the compilation unit and reuse the old java folder,
        // for ensure interdepences to other files
        for (CompilationUnit cu : javaCUs.keySet()) {
            final SpecificationInjector si =
                new SpecificationInjector(sc, JPF.getServiceConfiguration().getSourceInfo());
            cu.accept(si);

            ClassDeclaration clazz = (ClassDeclaration) cu.getPrimaryTypeDeclaration();
            for (MethodDeclaration mdecl : si.getSpecifiedMethodDeclarations()) {
                final StringBuilder sb = new StringBuilder();
                sb.append(formatAsList(mdecl.getParameters(), "", ",", ""));

                String poname = clazz.getFullName() + "[" + clazz.getFullName() + "\\\\:\\\\:"
                    + mdecl.getName() + "(" + sb + ")" + "]" + ".Non-interference contract.0";

                Path problemFileName =
                    javaRoot.resolveSibling(riflFilename.getFileName() + "_" + counter++ + ".key");

                writeProblemFile(problemFileName,
                    getDefaultSavePath(javaRoot).getFileName().toString(), poname);
                result.add(problemFileName);

            }
        }


        // step 3: write modified Java files
        for (Map.Entry<CompilationUnit, Path> javaUnit : javaCUs.entrySet()) {
            CompilationUnit cu = javaUnit.getKey();
            Path relative = javaUnit.getValue();
            writeJavaFile(savePath.resolve(relative), cu);
        }

    }


    private void writeProblemFile(Path problemFileName, String newJavaFolder, String poname) {
        String tmp;
        StringBuilder blueprint = new StringBuilder();

        final var stream = getClass().getResourceAsStream("blueprint_rifl.key");
        Objects.requireNonNull(stream);

        try (BufferedReader br =
            new BufferedReader(new InputStreamReader(stream, StandardCharsets.UTF_8));
                Writer fw = Files.newBufferedWriter(problemFileName, StandardCharsets.UTF_8)) {
            while ((tmp = br.readLine()) != null) {
                blueprint.append(tmp).append("\n");
            }

            fw.write(blueprint.toString().replace("%%JAVA_SOURCE%%", newJavaFolder)
                    .replace("%%PO_NAME%%", poname));
        } catch (IOException e) {
            LOGGER.warn("Failed to write problem file", e);
        }
    }

    private void ensureTargetDirExists(Path target) throws IOException {
        if (Files.exists(target)) {
            if (!Files.isDirectory(target) || !Files.isWritable(target)) { // bad
                throw new IOException("target directory " + target + " not writable");
            }
        } else { // create directory
            Files.createDirectories(target);
        }
    }

    /**
     * Writes a single Java file.
     */
    private void writeJavaFile(Path target, CompilationUnit cu) throws IOException {
        try (var writer = Files.newBufferedWriter(target, StandardCharsets.UTF_8)) {
            LOGGER.debug("Trying to write file {}", target);
            final String source = cu.toSource();

            LOGGER.debug("[RIFL] Write the following contents to file:");
            LOGGER.debug(source);

            writer.write(source);
            writer.flush();
        }
    }


    public List<Path> getProblemFiles() {
        return result;
    }
}
