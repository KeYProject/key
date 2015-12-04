package org.key_project.key4eclipse.resources.property;

import org.eclipse.core.resources.IProject;

public class KeYProjectBuildProperties {

   private final boolean enableKeyResourcesBuilds;
   private final boolean buildOnStartUp;
   private final boolean buildRequiredProofsOnly;
   private final boolean enableMultiThreading;
   private final int numberOfThreads;
   private final boolean autoDeleteProofFiles;
   private final boolean generateTestCases;
   private final boolean autoDeleteTestCases;
   private final boolean generateCounterExamples;
   
   public KeYProjectBuildProperties(IProject project) {
      super();
      this.enableKeyResourcesBuilds = KeYProjectProperties.isEnableKeYResourcesBuilds(project);
      this.buildOnStartUp = KeYProjectProperties.isEnableBuildOnStartup(project);
      this.buildRequiredProofsOnly = KeYProjectProperties.isEnableBuildRequiredProofsOnly(project);
      this.enableMultiThreading = KeYProjectProperties.isEnableMultiThreading(project);
      this.numberOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      this.autoDeleteProofFiles = KeYProjectProperties.isAutoDeleteProofFiles(project);
      this.generateTestCases = KeYProjectProperties.isGenerateTestCases(project);
      this.autoDeleteTestCases = KeYProjectProperties.isAutoDeleteTestCases(project);
      this.generateCounterExamples = KeYProjectProperties.isGenerateCounterExamples(project);
   }
   
   public boolean isEnableKeYResourcesBuilds() {
      return enableKeyResourcesBuilds;
   }
   public boolean isBuildOnStartUp() {
      return buildOnStartUp;
   }
   public boolean isBuildRequiredProofsOnly() {
      return buildRequiredProofsOnly;
   }
   public boolean isEnableMultiThreading() {
      return enableMultiThreading;
   }
   public int getNumberOfThreads() {
      return numberOfThreads;
   }
   public boolean isAutoDeleteProofFiles() {
      return autoDeleteProofFiles;
   }
   public boolean isGenerateTestCases() {
      return generateTestCases;
   }
   public boolean isAutoDeleteTestCases() {
      return autoDeleteTestCases;
   }
   public boolean isGenerateCounterExamples() {
       return generateCounterExamples;
    }   
}
