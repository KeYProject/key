package de.uka.ilkd.key.proof.io.consistency;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;

/**
 * This class uses a temporary directory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
public class DiskFileRepo extends AbstractFileRepo {
    protected final Path KEYPATH=Paths.get("/home/wolfram/Schreibtisch/Hiwi/KeY/key/key/key.core/bin/");
    protected final Path tmpDir;
    protected Path baseDir;
    /**
     * Stores for each requested path the mapping to its concrete path in temp dir. 
     */
    protected final HashMap<Path,Path> map = new HashMap<Path,Path>();

    /**
     * Stores all files which have been requested to the repo.
     */
    protected final Set<Path> files = new HashSet<Path>();

    public DiskFileRepo(String proofName) throws IOException {
        tmpDir = Files.createTempDirectory(proofName);
        System.out.println(tmpDir);
    }
    
    /*
     * getFile:
     * input: path (rel/abs) of a file
     * 
     * java file or key/proof file?
     * java: already in map? -> yes: return from map
     *       no:
     *       match path to jp/cp/bcp
     *       relativize path
     *       add to tmp dir (jp/cp/bcp)
     *       add to map
     * key/proof:
     *       already in map? -> yes: return from map
     *       no:
     *       add to root of tmp dir
     *       add to map
     */
    
    // TODO: adapt references to file ("\\includeFile") in .key/.proof files
    // TODO: try to keep original directory structure?
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
               if (norm.startsWith(KEYPATH) || baseDir == null) {
                   rel = KEYPATH.relativize(norm);
                   newFile = tmpDir.resolve(rel);
               } else {
                   rel = baseDir.relativize(norm);
                   newFile = tmpDir.resolve(rel);
               }
               System.out.println("Copying " + norm + " to " + newFile);
               if (!Files.exists(newFile.getParent())) {
                   Files.createDirectories(newFile.getParent());
               }
               Files.copy(norm, newFile);
               map.put(norm, newFile);
               files.add(newFile);
               adaptFileRefs(newFile);     // TODO: currently only a stub
           }
       }
       return null;
    }

    @Override
    public void setBaseDir(Path path) {
        // path can be a file or a directory
        if (Files.isDirectory(path)) {
            baseDir = path.toAbsolutePath();
        } else {
            baseDir = path.getParent().toAbsolutePath();
        }
    }

    @Override
    public RuleSource getRuleSource(Path p) {
        try {
            // file request to store the file with the given path in the repo
            getFile(p);
        }
        catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        // create a new FileRuleSource pointing to the copy (!) in the FileRepo
        return RuleSourceFactory.initRuleFile(map.get(p).toFile());
    }

    private static void adaptFileRefs(Path path) {
        // TODO: search for "\\include", "\\includeFile", "\\javaSource", "\\classPath", "\\bootClassPath",
        //              "\\includeLDT", other?
        //    and replace them by correct references
    }

    @Override
    public void saveProof(Path path, Proof proof) throws IOException {
        // TODO: Create ZIP archive with all relevant files
        // structure:
        // ZIP_Proof
        //      src/
        //      classpath/
        //      bootclasspath/
        // .proof
        // .key
        
        // create actual ZIP file
        Files.createDirectories(path.getParent());
        Files.createFile(path);
        
        // save files to ZIP
        ZipOutputStream zos = new ZipOutputStream(Files.newOutputStream(path));
        Iterator<Path> it = files.iterator();
        while (it.hasNext()) {
            Path p = it.next();
            System.out.println("Writing " + tmpDir.relativize(p));
            zos.putNextEntry(new ZipEntry(tmpDir.relativize(p).toString()));
            Files.copy(p, zos);
            zos.closeEntry();
        }
        zos.close();
    }

    private static void printFile(InputStream is) {
        int i = 0;
        try {
            i = is.read();
            while (i != -1) {
                System.out.print((char)i);
                i = is.read();
            }
            is.close();
            }
            catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
    }
   
    public static void main(String[] args) {
        try {
            
            System.out.println(Paths.get("demoFileRepo"));
            DiskFileRepo dfr = new DiskFileRepo("demoFileRepo");
            dfr.setJavaPath(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/"));
            
            //printFile(dfr.getFile(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/Highlight.java")));
            //printFile(dfr.getFile(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/Second.java")));
            //printFile(dfr.getFile(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/Highlight.java")));
            dfr.getFile(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/Highlight.java"));
            dfr.getFile(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/Second.java"));
            dfr.getFile(Paths.get("/home/wolfram/Schreibtisch/1457Highlight/Highlight.java"));
            dfr.saveProof(Paths.get("/tmp/test" + System.currentTimeMillis()  + ".zip"), null);
            
            
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
