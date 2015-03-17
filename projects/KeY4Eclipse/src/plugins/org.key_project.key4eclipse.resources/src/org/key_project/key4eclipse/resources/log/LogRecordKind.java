package org.key_project.key4eclipse.resources.log;


/**
 * The different kinds of {@link LogRecord}s.
 * @author Martin Hentschel
 */
public enum LogRecordKind {
   /**
    * Times logged by the {@link KeYProjectBuilder#build(int, Map<String, String>, IProgressMonitor)}.
    */
   BUILD, 
   
   /**
    * Times logged by {@link KeYProjectBuilder#clean(IProgressMonitor)}
    */
   CLEAN, 

   /**
    * Times logged by {@link KeYProjectBuildJob}.
    */
   JOB
}
