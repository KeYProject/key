package org.key_project.key4eclipse.resources.log;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;

public final class KeYProjectLogger {

//   private Date buildDate;
//   
//   private int proofOblsAvailable;
//   
//   private int proofsDone;
//   
//   private long parseTimeStart;
//   private long parseTimeEnd;
//   
//   private long proofTimeStart;
//   private long prooftimeEnd;
//   
//   private long buildTimeStart;
//   private long buildTimeEnd;
   
   private final static String lineSeperator1 = "---------------------------------------------------------\n";
   private final static String lineSeperator2 = "#########################################################\n";

   public static void logBuild(IProject project, IResourceDelta delta) throws CoreException{
      Date date = new Date();
      SimpleDateFormat sdf = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss");
      String dateStr = sdf.format(date) + "\n";
      
      
      String settingsStr = "Settings:\n"
                           + "Build proofs = " + KeYProjectProperties.isEnableBuildProofs(project) + "\n"
                           + "Build required proofs only = " + KeYProjectProperties.isEnableBuildRequiredProofsOnly(project) + "\n"
                           + "MultiThreading = " + KeYProjectProperties.isEnableMultiThreading(project) + "\n"
                           + "Number of threads = " + KeYProjectProperties.getNumberOfThreads(project) + "\n"
                           + "Auto delete proof files = " + KeYProjectProperties.isAutoDeleteProofFiles(project) + "\n"
                           + "Hide meta files = " + KeYProjectProperties.isHideMetaFiles(project) + "\n";
      String resChangesStr = "";
      if(delta!=null){
         KeYProjectLoggerDeltaVisitor kpldv = new KeYProjectLoggerDeltaVisitor();
         delta.accept(kpldv);
      
      
      
         resChangesStr = "Resource changes:\n\n"
                        + "Changed files = " + kpldv.getChangedFiles() + "\n"
                        + kpldv.getChagedFilesStr() + "\n"
                        + "New files = " + kpldv.getAddedFiles() + "\n"
                        + kpldv.getAddedFilesStr() + "\n"
                        + "Deleted files = " + kpldv.getRemovedFiles() + "\n"
                        + kpldv.getRemovedFilesStr() + "\n";
      
      }
      save(project, dateStr + lineSeperator1 + settingsStr + lineSeperator1 + resChangesStr);
   }
   
   public static void logBuild2(IProject project, int proofObls, List<Integer> proofsDone, long parseTimeStart, long parseTimeEnd, long proofTimeStart, long proofTimeEnd){
      String numOblsStr = "Number of proofObls = " + proofObls + "\n";
      int proofsDoneSum = 0;
      for(int i : proofsDone){
         proofsDoneSum += i;
      }
      String proofsDoneStr = "Number of proofs done = " + proofsDoneSum + "\n";
      
      long totalParseTime = parseTimeEnd - parseTimeStart;
      String parseTimeStr = "Parse time = " + totalParseTime + "ms\n";
      
      long totalProofTime = proofTimeEnd - proofTimeStart;
      String proofTimeStr = "Proof time = " + totalProofTime + "ms\n";
      
       save(project, lineSeperator1 + numOblsStr + proofsDoneStr + "\n" + parseTimeStr + proofTimeStr);
   }
   
   public static void logBuild3(IProject project, long buildTimeStart, long buildTimeEnd){
      long totalBuildTime = buildTimeEnd-buildTimeStart;
      String buildTimeStr = "Build time: " + totalBuildTime + "\n";
      save(project, buildTimeStr + "\n" + lineSeperator1 + lineSeperator2 + lineSeperator1 + "\n");
   }
   
   private static void save(IProject project, String str){
      try {
         ByteArrayOutputStream baos = new ByteArrayOutputStream();
         DataOutputStream dos = new DataOutputStream(baos);
         dos.writeBytes(str);
         dos.close();
         ByteArrayInputStream bais = new ByteArrayInputStream(baos.toByteArray());
         
         IFolder logFolder = project.getFolder("/proofLog");
         if(!logFolder.exists()){
            logFolder.create(true, true, null);
         }
         IFile logFile = project.getFile("proofLog/log.txt");
         if(!logFile.exists()){
            logFile.create(bais, true, null);
         }
         else{
            logFile.appendContents(bais, true, true, null);
         }
      }
      catch (IOException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      catch (CoreException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }
}
