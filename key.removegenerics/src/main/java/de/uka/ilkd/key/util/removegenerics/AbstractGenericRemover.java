package de.uka.ilkd.key.util.removegenerics;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.PathList;
import recoder.java.CompilationUnit;
import de.uka.ilkd.key.util.removegenerics.monitor.GenericRemoverMonitor;

public abstract class AbstractGenericRemover {
   private final GenericRemoverMonitor monitor;

   private final CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();

   private final Map<CompilationUnit, String> allUnits = new LinkedHashMap<CompilationUnit, String>();

   private final List<String> sourceFiles = new ArrayList<String>();
   
   public AbstractGenericRemover(GenericRemoverMonitor monitor) {
      assert monitor != null;
      this.monitor = monitor;
   }
   
   public void addSearchPath(String path) {
      PathList searchPaths = sc.getProjectSettings().getSearchPathList();
      searchPaths.add(path);
   }
   
   public void addSourceFiles(Collection<String> sourceFiles) {
      sourceFiles.addAll(sourceFiles);
   }

   public void addSourceFile(String file) {
      sourceFiles.add(file);
   }
   
   public PathList getSearchPath() {
      return sc.getProjectSettings().getSearchPathList();
   }
   
   public List<String> getSourceFiles() {
      return sourceFiles;
   }

   public void removeGenerics() throws ParserException, IOException {
      for (String fileName : sourceFiles) {
         File file = new File(fileName);
         if (file.isDirectory())
             processDirectory(file);
         else
             processFile(file);
     }

     List<ResolveGenerics> allTransformations = new ArrayList<ResolveGenerics>();

     monitor.taskStarted("Analysing ...");

     sc.getChangeHistory().updateModel();

     for (CompilationUnit cu : allUnits.keySet()) {
         ResolveGenerics transformation = new ResolveGenerics(sc, cu);

         // add also the empty transformation ... so that unchanged files are
         // copied
         transformation.analyze();
         allTransformations.add(transformation);
     }

     monitor.taskStarted("Transformation ...");
     for (ResolveGenerics transformation : allTransformations) {
         transformation.transform();
         CompilationUnit cu = transformation.getCU();

         // repair spacing around single line comments
         SingleLineCommentRepairer.repairSingleLineComments(cu);

         // save new content
         String filename = allUnits.get(cu);
         saveModifiedCompilationUnit(cu, filename);
     }
     
     monitor.taskStarted("Remove Generics completed.");
   }

   protected abstract void saveModifiedCompilationUnit(CompilationUnit cu, String filename) throws IOException;

   private void processDirectory(File dir) throws ParserException {

       for (File f : dir.listFiles()) {
           if (f.isDirectory())
               processDirectory(f);
           else if (f.getName().toLowerCase().endsWith(".java"))
               processFile(f);
       }

   }

   private void processFile(File file) throws ParserException {
       monitor.taskStarted("Reading from " + file);
       if (!file.exists()) {
           monitor.warningOccurred(file + " does not exist");
           return;
       }

       if (!file.canRead()) {
           monitor.warningOccurred(file + " cannot be read");
           return;
       }

       CompilationUnit cu = sc.getSourceFileRepository().getCompilationUnitFromFile(file.getPath());
       String filename = file.getName();

       allUnits.put(cu, filename);
   }
}
