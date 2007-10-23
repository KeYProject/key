package de.uka.ilkd.key.util.removegenerics;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.PathList;
import recoder.java.CompilationUnit;
import recoder.java.PackageSpecification;
import recoder.java.reference.PackageReference;
import recoder.kit.TwoPassTransformation;

public class Main {

    private static CrossReferenceServiceConfiguration sc;

    private static File outDir = new File(".");

    private static LinkedHashMap<CompilationUnit, String> allUnits = new LinkedHashMap<CompilationUnit, String>();

    public static boolean dbg = false;

    /**
     * @param args
     * @throws
     */
    public static void main(String[] args) throws Exception {
        
        System.out.println("Version - 071019 - 1546");

        sc = new CrossReferenceServiceConfiguration();

        PathList searchPaths = sc.getProjectSettings().getSearchPathList();

        List<String> files = new ArrayList<String>();

        for (int i = 0; i < args.length; i++) {

            try {
                if (args[i].equals("-d")) {
                    outDir = new File(args[++i].trim());
                } else if (args[i].equals("-classpath") || args[i].equals("-cp")) {
                    for (String s : args[++i].split(File.pathSeparator))
                        searchPaths.add(s);
                } else if (args[i].startsWith("@")) {
                    addLinesFromFile(args[i].substring(1), files);
                } else if(args[i].equals("-v")){
                    GenericResolutionTransformation.DEBUG_OUTPUT = true;
                } else {
                    files.add(args[i]);
                }
            } catch (IndexOutOfBoundsException e) {
                System.err.println("Argument " + args[i - 1] + " needs a parameter");
            }

        }
        
        if(!outDir.exists()) {
            System.err.println("The output directory does not exist");
            System.exit(1);
        }

        for (String fileName : files) {
            File file = new File(fileName);
            if (file.isDirectory())
                processDirectory(file);
            else
                processFile(file);
        }

        List<ResolveGenerics> allTransformations = new ArrayList<ResolveGenerics>();
        
        System.out.println("Analysing ...");
        
        sc.getChangeHistory().updateModel();
        
        for (CompilationUnit cu : allUnits.keySet()) {
            ResolveGenerics transformation = new ResolveGenerics(sc, cu);
            
            // add also the empty transformation ... so that unchanged files are copied
            transformation.analyze();
            allTransformations.add(transformation);
        }
        
        System.out.println("Transformation ...");
        for(ResolveGenerics transformation : allTransformations) {
            transformation.transform();
            CompilationUnit cu = transformation.getCU();
            
            // repair spacing around single line comments
            SingleLineCommentRepairer.repairSingleLineComments(cu);
            
            // determine target subdirectory with trailing '/'
            File targetdir;
            PackageSpecification packageSpecification = cu.getPackageSpecification();
            if(packageSpecification != null) {
                String pack = toString(packageSpecification.getPackageReference());
                String subdir = pack.replace('.', File.separatorChar);
                targetdir = new File(outDir, subdir);
            } else {
                targetdir = outDir;
            }
            
            // retrieve filename
            String filename = allUnits.get(cu);
            File outFile = new File(targetdir, filename);
            
            // make directory if not existant
            targetdir.mkdirs();

            GenericResolutionTransformation.debugOut("output file", outFile);
            
            Writer w = new FileWriter(outFile);
            w.write(cu.toSource());
            w.close();
        }

    }

    private static String toString(PackageReference packageReference) {
        
        String ret = packageReference.getIdentifier().getText();
        packageReference = packageReference.getPackageReference();
        
        while(packageReference != null)
        do {
            ret = packageReference.getIdentifier().getText() + "." + ret;
            packageReference = packageReference.getPackageReference();
        } while(packageReference != null);
        
        return ret;
    }

    private static void addLinesFromFile(String file, List<String> files) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(file));

        String line = br.readLine();
        while (line != null) {
            line = line.trim();
            if (!line.startsWith("#"))
                files.add(line);
        }
    }

    private static void processDirectory(File dir) throws ParserException {

        for (File f : dir.listFiles()) {
            if (f.isDirectory())
                processDirectory(f);
            else if (f.getName().toLowerCase().endsWith(".java"))
                processFile(f);
        }

    }

    private static void processFile(File file) throws ParserException {
        System.out.println("Reading from " + file);
        if (!file.exists()) {
            System.out.println(" ... does not exist");
            return;
        }
        
        if (!file.canRead()) {
            System.out.println(" ... cannot be read");
            return;
        }

        CompilationUnit cu = sc.getSourceFileRepository().getCompilationUnitFromFile(file.getPath());
        String filename = file.getName();
        
        allUnits.put(cu, filename);
    }

}
