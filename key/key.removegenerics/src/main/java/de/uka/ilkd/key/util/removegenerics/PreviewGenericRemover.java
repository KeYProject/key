package de.uka.ilkd.key.util.removegenerics;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import recoder.io.DataFileLocation;
import recoder.io.DataLocation;
import recoder.java.CompilationUnit;
import de.uka.ilkd.key.util.removegenerics.monitor.GenericRemoverMonitor;

public class PreviewGenericRemover extends AbstractGenericRemover {
   private final Map<File, String> resultMap = new HashMap<File, String>();

   public PreviewGenericRemover(GenericRemoverMonitor monitor) {
      super(monitor);
   }

   @Override
   protected void saveModifiedCompilationUnit(CompilationUnit cu, String filename) throws IOException {
      DataLocation location = cu.getDataLocation();
      assert location instanceof DataFileLocation;
      DataFileLocation fileLocation = (DataFileLocation) location;
      resultMap.put(fileLocation.getFile(), cu.toSource());
   }

   public Map<File, String> getResultMap() {
      return resultMap;
   }
}
