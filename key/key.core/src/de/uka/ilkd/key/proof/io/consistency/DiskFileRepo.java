package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;

/**
 * This class uses a temporary directory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
public class DiskFileRepo extends AbstractFileRepo {
    /**
     * The path where KeY's built-in rules are stored.
     * Needed to prevent built-in rules from getting cached.
     */
    protected static final Path KEYPATH=RuleSourceFactory.fromDefaultLocation("").file().toPath();

    /**
     * The temporary directory used as a cache.
     */
    protected Path tmpDir;

    /**
     * Stores for each requested path the mapping to its concrete path in temp dir. 
     */
    protected HashMap<Path,Path> map = new HashMap<Path,Path>();

    /**
     * Stores paths of all files stored in the repo.
     */
    protected Set<Path> files = new HashSet<Path>();        // TODO: set unnecessary?, list may be better

    public DiskFileRepo(String proofName) throws IOException {
        tmpDir = Files.createTempDirectory(proofName);
        System.out.println(tmpDir);
    }

    // TODO: care about links
    @Override
    public InputStream getFile(Path path) throws FileNotFoundException, IOException {
       System.out.println("getFile() -> path: " + path);
       final Path norm = path.toAbsolutePath().normalize();
       
       final Path p = map.get(norm);
       System.out.println("    norm: " + norm + "\n    p: " + p);
       if (p != null) {                             // already in map -> everything already done
           System.out.println("    Already existing: " + p);
           return new FileInputStream(p.toFile());
       } else {                                     // create new temp file
           // where is the file?
           // .java files: (javapath, classpath, bootclasspath)
           // .proof/.key files
           FileSystem fs = FileSystems.getDefault();
           if (fs.getPathMatcher("glob:**.java").matches(norm)) {                // *.java
               if (javaPath != null && norm.startsWith(javaPath)) {
                   Path srcDir = tmpDir.resolve(Paths.get("src"));
                   final Path rel = javaPath.relativize(norm);
                   System.out.println("    rel: " + rel);
                   System.out.println("    srcDir: " + srcDir);

                   Path newFile = srcDir.resolve(rel);
                   
                   if (!Files.exists(newFile.getParent())) {       // create parent dir if not existing
                       Files.createDirectories(newFile.getParent());
                   }
                   
                   System.out.println("    Copying " + norm + " to " + newFile);
                   Files.copy(norm, newFile);

                   System.out.println("    Put to map: key: " + norm.getFileName() + " val: " + newFile);
                   map.put(norm, newFile);
                   files.add(newFile);

                   return new FileInputStream(newFile.toFile());
               } else if (classPath != null && norm.startsWith(classPath)) {
                   System.out.println("Not yet implemented: CP");
               } else if (bootClassPath != null && norm.startsWith(bootClassPath)) {
                   System.out.println("Not yet implemented: BCP");
               } else {
                   // TODO: should not happen
                   System.out.println("Should not happen");
               }
           } else if (fs.getPathMatcher("glob:**.{key,proof}").matches(norm)) {  //.key/.proof
               Path newFile;
               final Path rel;
               if (isBuiltInRuleFile(norm) || baseDir == null) {            // don't cache
                   System.out.println("        internal rule file (don't cache)!");
                   map.put(path, path);
                   return new FileInputStream(path.toFile());               // InputStream from original file!
               }
               
               rel = baseDir.relativize(norm);
               newFile = tmpDir.resolve(rel);
               
               System.out.println("Copying " + norm + " to " + newFile);
               if (!Files.exists(newFile.getParent())) {
                   Files.createDirectories(newFile.getParent());
               }
               Files.copy(norm, newFile);
               map.put(norm, newFile);
               files.add(newFile);
               //adaptFileRefs(newFile);        // TODO: do this when saving proof
               return new FileInputStream(newFile.toFile());
           }
       }
       return null;
    }

//    @Override
//    public RuleSource getRuleSource(Path p) {
//        try {
//            // file request to store the file with the given path in the repo
//            getFile(p);
//
//            // create a new FileRuleSource pointing to the copy (!) in the FileRepo
//            return RuleSourceFactory.initRuleFile(map.get(p).toFile());
//        }
//        catch (FileNotFoundException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//        }
//        catch (IOException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//        }
//        
//        return null;
//    }

    // InputStream getInputStream(RuleSource rs) {
    //      TODO: case distinction URL/File
    // }

    /**
     * Rewrites the file references inside of .key/.proof files such that the point correctly to
     * the copied files in the ZIP file.
     * @param path the path of the file where the references are adapted
     */
    private static void adaptFileRefs(Path path) {
        // TODO: search for "\\include", "\\includeFile", "\\javaSource", "\\classPath", "\\bootClassPath",
        //              "\\includeLDT", other?
        //    and replace them by correct references
        PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**.{key,proof}");
        if (matcher.matches(path)) {
            try (Stream<String> lines = Files.lines(path)) {
                List<String> rep = lines.map(
                        // TODO: line break removed here!
                        // TODO: semicolon may be part of filename
                        l -> l.replaceAll("\\\\javaSource [^;\\n\\r]*;", "\\\\javaSource \"src\";"))
                        .collect(Collectors.toList());
                Files.write(path, rep);
                lines.close();
                System.out.println("new javaSource written!");
            }
            catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
    }

    private static boolean isBuiltInRuleFile(Path file) {
        // TODO: check for URL
        return file.normalize().startsWith(KEYPATH);
    }

    @Override
    public void saveProof(Path path, Proof proof) throws IOException {
        // create actual ZIP file (plus its directory if not existent)
        Files.createDirectories(path.getParent());
        Files.createFile(path);
        
        PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**.{key,proof}");
        
        // write files to ZIP
        ZipOutputStream zos = new ZipOutputStream(Files.newOutputStream(path));
        Iterator<Path> it = files.iterator();
        while (it.hasNext()) {
            Path p = it.next();
            if (matcher.matches(p)) {  // adapt file references to point to the copied files
                adaptFileRefs(p);
            }
            System.out.println("Writing " + tmpDir.relativize(p));
            zos.putNextEntry(new ZipEntry(tmpDir.relativize(p).toString()));
            Files.copy(p, zos);
            zos.closeEntry();
        }
        zos.close();
    }

    @Override
    public void dispose() {
        if (disposed) {
            return;
        }

        try {
            // delete the temporary directory with all contained files
            Files.walk(baseDir)
                .sorted(Comparator.reverseOrder())
                .map(Path::toFile)
                .forEach(File::delete);
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // set every hold reference to null
        tmpDir = null;
        map = null;
        files = null;
        super.dispose();
    }
}
