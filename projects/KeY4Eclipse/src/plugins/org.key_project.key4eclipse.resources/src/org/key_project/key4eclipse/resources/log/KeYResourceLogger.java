package org.key_project.key4eclipse.resources.log;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.LogUtil;

public final class KeYResourceLogger {
   
   private final static String lineSeperator = "#########################################################\n";
   
   public static void logNeWBuild(IProject project, IResourceDelta delta){
      Date date = new Date();
      SimpleDateFormat sdf = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss");
      String dateStr = "New Build started at " + sdf.format(date) + "\n\n";
      
      String settingsStr = "";
      
      try{
         settingsStr = "   Settings:\n"
            + "      Build proofs = " + KeYProjectProperties.isEnableBuildProofs(project) + "\n"
            + "      Build required proofs only = " + KeYProjectProperties.isEnableBuildRequiredProofsOnly(project) + "\n"
            + "      MultiThreading = " + KeYProjectProperties.isEnableMultiThreading(project) + "\n"
            + "      Number of threads = " + KeYProjectProperties.getNumberOfThreads(project) + "\n"
            + "      Auto delete proof files = " + KeYProjectProperties.isAutoDeleteProofFiles(project) + "\n"
            + "      Hide meta files = " + KeYProjectProperties.isHideMetaFiles(project) + "\n\n";
      
      } catch (CoreException e){
         LogUtil.getLogger().logError(e);
      }
      
      String resChangesStr = "";
      
      if(delta!=null){
         KeYResourceLoggerDeltaVisitor krldv = new KeYResourceLoggerDeltaVisitor();
         try{
            delta.accept(krldv);
            
            resChangesStr  = "   Resource changes:\n";
            
            LinkedList<String> files = krldv.getChagedFiles();
            resChangesStr += "      Changed files = " + files.size() + "\n";
            for(String str : files){
               resChangesStr += "         " + str + "\n";
            }

            files = krldv.getAddedFiles();
            resChangesStr += "      New files = " + files.size() + "\n";
            for(String str : files){
               resChangesStr += "         " + str + "\n";
            }
            
            files = krldv.getRemovedFiles();
            resChangesStr += "      Deleted files = " + files.size() + "\n";
            for(String str : files){
               resChangesStr += "         " + str + "\n";
            }
            
         } catch (CoreException e){
            LogUtil.getLogger().logError(e);
         }
      }
      
      save(project, lineSeperator + "\n" + dateStr + settingsStr + resChangesStr + "\n\n");
   }
   
   public static void logBuild(IProject project, int numOfProofs, List<Integer> proofsDone, long parseTimeStart, long parseTimeEnd, long proofTimeStart, long proofTimeEnd){
      String numOblsStr = "   Number of proofs found = " + numOfProofs + "\n";
      int proofsDoneSum = 0;
      for(int i : proofsDone){
         proofsDoneSum += i;
      }
      String proofsDoneStr = "   Number of proofs done = " + proofsDoneSum + "\n";
      
      long totalParseTime = parseTimeEnd - parseTimeStart;
      String parseTimeStr = "   Parse time = " + totalParseTime + "ms\n";
      
      long totalProofTime = proofTimeEnd - proofTimeStart;
      String proofTimeStr = "   Proof time = " + totalProofTime + "ms\n";
      
       save(project, numOblsStr + proofsDoneStr + "\n" + parseTimeStr + proofTimeStr);
   }
   
   public static void logBuildTime(IProject project, long buildTime){
      String buildTimeStr = "   Build time: " + buildTime;
      save(project, buildTimeStr + "\n\n" + lineSeperator + "\n");
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
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
}
