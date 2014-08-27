package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import java.io.File;
import java.io.FileOutputStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.junit.Before;
import org.junit.Test;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.test.testcase.junit.AbstractResourceTest;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.ui.provider.ProjectInfoColorTreeSynchronizer;
import org.key_project.key4eclipse.resources.ui.test.Activator;
import org.key_project.key4eclipse.resources.ui.view.VerificationStatusView;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.SWTBotCustomProgressBar;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTBot tests for {@link VerificationStatusView}.
 * @author Martin Hentschel
 */
public class SWTBotVerificationStatusViewTest extends AbstractResourceTest {
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      // Ensure that no other KeY project is open
      IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
      for (IProject project : projects) {
         if (KeYResourcesUtil.isKeYProject(project)) {
            project.close(null);
         }
      }
   }

   /**
    * Tests the information about taclet options
    * <ol>
    *    <li>Proof with just informations about taclet options</li>
    *    <li>Proof with incomplete taclet options</li>
    *    <li>Proof with unsound taclet options</li>
    * </ol>
    * @throws Exception
    */
   @Test
   public void testTacletOptions() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         SWTBotCustomProgressBar proofBar = SWTBotCustomProgressBar.customProgressBar(bot, 0);
         SWTBotCustomProgressBar specificationBar = SWTBotCustomProgressBar.customProgressBar(bot, 1);
         // Test initial project
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testTacletOptions", true, true, false, 1, true, true);
         IFolder srcFolder = project.getFolder("src");
         assertTrue(srcFolder.exists());
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/tacletOptions/src", srcFolder, true);
         IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/tacletOptions/info", proofFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         // Find content
         ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
         PackageInfo packageInfo = projectInfo.getPackage(PackageInfo.DEFAULT_NAME);
         TypeInfo typeInfo = packageInfo.getType("Magic");
         MethodInfo methodInfo = typeInfo.getMethod("magic()");
         ContractInfo contractInfo = methodInfo.getContract(0);
         Map<Object, RGB> colorMapping = new HashMap<Object, RGB>();
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(methodInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(contractInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         // Ensure initial content
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, false, 1, 1, specificationBar, true, false, 1, 2);
         assertReport(view, "data/tacletOptions/oracle/Report1Info.html");
         // Change proof
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/tacletOptions/incomplete", proofFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, false, 1, 1, specificationBar, true, false, 1, 2);
         assertReport(view, "data/tacletOptions/oracle/Report2Incomplete.html");
         // Change proof
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/tacletOptions/unsound", proofFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, false, 1, 1, specificationBar, true, false, 1, 2);
         assertReport(view, "data/tacletOptions/oracle/Report3Unsound.html");
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }
   
   /**
    * Tests the priority of colors.
    * @throws Exception
    */
   @Test
   public void testColorPriorization() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         SWTBotCustomProgressBar proofBar = SWTBotCustomProgressBar.customProgressBar(bot, 0);
         SWTBotCustomProgressBar specificationBar = SWTBotCustomProgressBar.customProgressBar(bot, 1);
         // Test initial project
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testColorPriorization", true, true, false, 1, true, true);
         IFolder srcFolder = project.getFolder("src");
         assertTrue(srcFolder.exists());
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/cp/src", srcFolder, true);
         IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/cp/proofs", proofFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         // Find content
         ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
         PackageInfo closedProofsPackage = projectInfo.getPackage("cl");
         PackageInfo cyclicProofsPackage = projectInfo.getPackage("cy");
         PackageInfo openProofsPackage = projectInfo.getPackage("op");
         PackageInfo unprovenDependencyPackage = projectInfo.getPackage("ud");
         PackageInfo unspecifiedPackage = projectInfo.getPackage("us");
         TypeInfo closedProofsType = closedProofsPackage.getType("CP");
         TypeInfo multipleRecursionType = cyclicProofsPackage.getType("MR");
         TypeInfo openProofType = openProofsPackage.getType("OP");
         TypeInfo unprovenDependencyType = unprovenDependencyPackage.getType("UD");
         TypeInfo unspecifiedType = unspecifiedPackage.getType("US");
         MethodInfo closedProofsCorrectMethod = closedProofsType.getMethod("correct()");
         MethodInfo multipleRecursionAMethod = multipleRecursionType.getMethod("a()");
         MethodInfo multipleRecursionBMethod = multipleRecursionType.getMethod("b()");
         MethodInfo multipleRecursionCorrectMethod = multipleRecursionType.getMethod("correct()");
         MethodInfo multipleRecursionCorrectUnprovenMethod = multipleRecursionType.getMethod("correctUnprovenDependency()");
         MethodInfo multipleRecursionUnspecifiedMethod = multipleRecursionType.getMethod("unspecified()");
         MethodInfo multipleRecursionWrongMethod = multipleRecursionType.getMethod("wrong()");
         MethodInfo openProofCorrectMethod = openProofType.getMethod("correct()");
         MethodInfo openProofCorrectUnprovenMethod = openProofType.getMethod("correctUnprovenDependency()");
         MethodInfo openProofWrongMethod = openProofType.getMethod("wrong()");
         MethodInfo unprovenDependencyCorrectMethod = unprovenDependencyType.getMethod("correct()");
         MethodInfo unprovenDependencyCorrectUnprovenMethod = unprovenDependencyType.getMethod("correctUnprovenDependency()");
         MethodInfo unspecifiedCorrectMethod = unspecifiedType.getMethod("correct()");
         MethodInfo unspecifiedCorrectUnprovenMethod = unspecifiedType.getMethod("correctUnprovenDependency()");
         MethodInfo unspecifiedUnspecifiedMethod = unspecifiedType.getMethod("unspecified()");
         Map<Object, RGB> colorMapping = new HashMap<Object, RGB>();
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(closedProofsPackage, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(cyclicProofsPackage, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(openProofsPackage, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(unprovenDependencyPackage, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(unspecifiedPackage, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(closedProofsType, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(multipleRecursionType, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(openProofType, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(unprovenDependencyType, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(unspecifiedType, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);

         colorMapping.put(closedProofsCorrectMethod, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(multipleRecursionAMethod, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(multipleRecursionBMethod, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(multipleRecursionCorrectMethod, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(multipleRecursionCorrectUnprovenMethod, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(multipleRecursionUnspecifiedMethod, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(multipleRecursionWrongMethod, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(openProofCorrectMethod, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(openProofCorrectUnprovenMethod, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(openProofWrongMethod, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(unprovenDependencyCorrectMethod, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(unprovenDependencyCorrectUnprovenMethod, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(unspecifiedCorrectMethod, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(unspecifiedCorrectUnprovenMethod, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(unspecifiedUnspecifiedMethod, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);

         colorMapping.put(closedProofsCorrectMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(multipleRecursionAMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(multipleRecursionBMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(multipleRecursionCorrectMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(multipleRecursionCorrectUnprovenMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(multipleRecursionUnspecifiedMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(multipleRecursionWrongMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(openProofCorrectMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(openProofCorrectUnprovenMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(openProofWrongMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(unprovenDependencyCorrectMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(unprovenDependencyCorrectUnprovenMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(unspecifiedCorrectMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(unspecifiedCorrectUnprovenMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(unspecifiedUnspecifiedMethod.getContract(0), ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         // Ensure initial content
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, true, true, 16, 18, specificationBar, true, false, 18, 20);
         assertReport(view, "data/cp/oracle/report.html");
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }
   
   /**
    * Tests the specification progress
    * <ol>
    *    <li>Class without methods</li>
    *    <li>Class with unspecified method</li>
    *    <li>Class with wrongly specified method</li>
    *    <li>Class with correctly specified method</li>
    * </ol>
    * @throws Exception
    */
   @Test
   public void testSpecificationAndProofProgress() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         SWTBotCustomProgressBar proofBar = SWTBotCustomProgressBar.customProgressBar(bot, 0);
         SWTBotCustomProgressBar specificationBar = SWTBotCustomProgressBar.customProgressBar(bot, 1);
         // Test initial project
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testSpecificationAndProofProgress", true, true, false, 1, true, true);
         IFolder srcFolder = project.getFolder("src");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/specificationProgress/src1NoMethod", srcFolder, true);
         assertTrue(srcFolder.exists());
         KeY4EclipseResourcesTestUtil.build(project);
         // Find content
         ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
         PackageInfo packageInfo = projectInfo.getPackage("myPackage");
         TypeInfo typeInfo = packageInfo.getType("MyClass");
         Map<Object, RGB> colorMapping = new HashMap<Object, RGB>();
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         // Ensure initial content
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, false, 1, 1, specificationBar, false, false, 1, 1);
         assertReport(view, "data/specificationProgress/oracle/Report1NoMethod.html");
         // Add unspecified method
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/specificationProgress/src2Unspecified", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         MethodInfo methodInfo = typeInfo.getMethod("magic()");
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         colorMapping.put(methodInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, false, 1, 1, specificationBar, true, false, 1, 2);
         assertReport(view, "data/specificationProgress/oracle/Report2Unspecified.html");
         // Specify method wrongly
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/specificationProgress/src3SpecifiedWrong", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         ContractInfo contractInfo = methodInfo.getContract(0);
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(methodInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(contractInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, true, false, 1, 2, specificationBar, false, false, 2, 2);
         assertReport(view, "data/specificationProgress/oracle/Report3SpecifiedWrong.html");
         // Correct specification
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/specificationProgress/src4SpecifiedCorrect", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(methodInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         colorMapping.put(contractInfo, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, false, 2, 2, specificationBar, false, false, 2, 2);
         assertReport(view, "data/specificationProgress/oracle/Report4SpecifiedCorrect.html");
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }

   /**
    * Tests in the color of cyclic proofs:
    * <ol>
    *    <li>Two open proofs are created</li>
    *    <li>First proof is closed with unproven dependency</li>
    *    <li>Second proof is closed forming a cycle</li>
    * </ol>
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testColorOfCyclicProofs() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         SWTBotCustomProgressBar proofBar = SWTBotCustomProgressBar.customProgressBar(bot, 0);
         SWTBotCustomProgressBar specificationBar = SWTBotCustomProgressBar.customProgressBar(bot, 1);
         // Test initial project
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testColorOfCyclicProofs", true, true, false, 1, true, true);
         IFolder srcFolder = project.getFolder("src");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/cyclicProofs/src", srcFolder, true);
         assertTrue(srcFolder.exists());
         KeY4EclipseResourcesTestUtil.build(project);
         // Find content
         ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
         PackageInfo packageInfo = projectInfo.getPackage("cp");
         TypeInfo typeInfo = packageInfo.getType("MR");
         MethodInfo aMethodInfo = typeInfo.getMethod("a()");
         ContractInfo aContractInfo = aMethodInfo.getContract(0);
         MethodInfo bMethodInfo = typeInfo.getMethod("a()");
         ContractInfo bContractInfo = bMethodInfo.getContract(0);
         Map<Object, RGB> colorMapping = new HashMap<Object, RGB>();
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(aMethodInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(aContractInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(bMethodInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         colorMapping.put(bContractInfo, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
         // Ensure that both proofs are open
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, true, false, 1, 3, specificationBar, false, false, 3, 3);
         assertReport(view, "data/cyclicProofs/oracle/Report1BothOpen.html");
         // Finish first proof
         IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/cyclicProofs/firstProof", proofFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         colorMapping.put(aMethodInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         colorMapping.put(aContractInfo, ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, true, false, 2, 3, specificationBar, false, false, 3, 3);
         assertReport(view, "data/cyclicProofs/oracle/Report2FirstClosed.html");
         // Finish second proof
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/cyclicProofs/secondProof", proofFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         colorMapping.put(project, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(packageInfo, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(typeInfo, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(aMethodInfo, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(aContractInfo, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(bMethodInfo, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         colorMapping.put(bContractInfo, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
         assertProjectShown(tree, colorMapping, project);
         assertProgressBars(proofBar, false, true, 3, 3, specificationBar, false, false, 3, 3);
         assertReport(view, "data/cyclicProofs/oracle/Report3BothClosed.html");
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }

   /**
    * Ensures that the correct HTML report is shown.
    * @param view The {@link SWTBotView} to test.
    * @param expectedOraclePathInBundle The expected oracle path in bundle.
    * @throws Exception Occurred Exception
    */
   protected void assertReport(SWTBotView view, String expectedOraclePathInBundle) throws Exception {
      assertReport(view, expectedOraclePathInBundle, "D:/Forschung/Development/SymbolicExecutionDebugger/junit-workspace");
   }

   /**
    * Ensures that the correct HTML report is shown.
    * @param view The {@link SWTBotView} to test.
    * @param expectedOraclePathInBundle The expected oracle path in bundle.
    * @param oracleWorkspacePath The path to the workspace used in oracle files.
    * @throws Exception Occurred Exception
    */
   protected void assertReport(SWTBotView view, String expectedOraclePathInBundle, String oracleWorkspacePath) throws Exception {
      // Get HTML report
      view.bot().cTabItem(1).activate();
      String htmlReport = ObjectUtil.toString(TestUtilsUtil.getData(view.bot().browser()));
      view.bot().cTabItem(0).activate();
      // Ensure that report is correct.
      if (oracleDirectory != null) {
         // Create sub folder structure
         File oracleFile = new File(oracleDirectory, expectedOraclePathInBundle);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         IOUtil.writeTo(new FileOutputStream(oracleFile), htmlReport);
         // Print message to the user.
         printOracleDirectory();
      }
      else {
         String expectedReport = IOUtil.readFrom(BundleUtil.openInputStream(Activator.PLUGIN_ID, expectedOraclePathInBundle));
         String workspacePath = ResourceUtil.getWorkspaceLocation().getAbsolutePath();
         workspacePath = workspacePath.replace(File.separatorChar, '/');
         expectedReport = expectedReport.replaceAll("D:/Forschung/Development/SymbolicExecutionDebugger/junit-workspace", workspacePath);
         if (!StringUtil.equalIgnoreWhiteSpace(expectedReport, htmlReport)) {
            assertEquals(expectedReport, htmlReport);
         }
      }
   }

   /**
    * Ensures that the progress bars in the correct state.
    * @param proofBar The {@link SWTBotCustomProgressBar} to test.
    * @param proofBarHasErrors The expected value.
    * @param proofBarIsStopped The expected value.
    * @param proofBarTicksDone The expected value.
    * @param proofBarMaximum The expected value.
    * @param specificationBar The {@link SWTBotCustomProgressBar} to test.
    * @param specificationBarHasErrors The expected value.
    * @param specificationBarIsStopped The expected value.
    * @param specificationBarTicksDone The expected value.
    * @param specificationBarMaximum The expected value.
    */
   protected void assertProgressBars(SWTBotCustomProgressBar proofBar, 
                                     boolean proofBarHasErrors, 
                                     boolean proofBarIsStopped, 
                                     int proofBarTicksDone, 
                                     int proofBarMaximum, 
                                     SWTBotCustomProgressBar specificationBar, 
                                     boolean specificationBarHasErrors, 
                                     boolean specificationBarIsStopped, 
                                     int specificationBarTicksDone, 
                                     int specificationBarMaximum) {
      assertEquals(proofBarHasErrors, proofBar.hasErrors());
      assertEquals(proofBarIsStopped, proofBar.isStopped());
      assertEquals(proofBarTicksDone, proofBar.getTicksDone());
      assertEquals(proofBarMaximum, proofBar.getMaximum());
      assertEquals(specificationBarHasErrors, specificationBar.hasErrors());
      assertEquals(specificationBarIsStopped, specificationBar.isStopped());
      assertEquals(specificationBarTicksDone, specificationBar.getTicksDone());
      assertEquals(specificationBarMaximum, specificationBar.getMaximum());
   }

   /**
    * Tests in particular packages and types.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testPackagesAndTypes() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         // Test empty project (step 0)
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testPackagesAndTypes", true, true, false, 1, true, true);
         assertProjectShown(tree, project);
         IFolder srcFolder = project.getFolder("src");
         assertTrue(srcFolder.exists());
         // Add empty classes in different packages (step 1)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/packagesAndTypes/step1/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add first method (step 2)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/packagesAndTypes/step2/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add more methods (step 3)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/packagesAndTypes/step3/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add remove methods and add new once (step 4)
         srcFolder.getFile("A.java").delete(true, null);
         srcFolder.getFile("ClassWithoutPackage.java").delete(true, null);
         srcFolder.getFile("Z.java").delete(true, null);
         srcFolder.getFolder("hello").getFile("A.java").delete(true, null);
         srcFolder.getFolder("hello").getFile("ClassInHello.java").delete(true, null);
         srcFolder.getFolder("hello").getFile("Z.java").delete(true, null);
         srcFolder.getFolder("hello").getFolder("world").getFile("ClassInHelloWorld.java").delete(true, null);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/packagesAndTypes/step4/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }

   /**
    * Tests in particular observer functions and contracts.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testObserverFunctionsAndContracts() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         // Test empty project (step 0)
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testObserverFunctionsAndContracts", true, true, false, 1, true, true);
         assertProjectShown(tree, project);
         IFolder srcFolder = project.getFolder("src");
         assertTrue(srcFolder.exists());
         // Add empty classes in different packages (step 1)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/observerFunctionsAndContracts/step1/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add first method (step 2)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/observerFunctionsAndContracts/step2/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add more methods (step 3)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/observerFunctionsAndContracts/step3/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add remove methods and add new once (step 4)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/observerFunctionsAndContracts/step4/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }

   /**
    * Tests in particular method contracts.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testMethodContracts() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         // Test empty project (step 0)
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testMethodContracts", true, true, false, 1, true, true);
         assertProjectShown(tree, project);
         IFolder srcFolder = project.getFolder("src");
         assertTrue(srcFolder.exists());
         // Add empty classes in different packages (step 1)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methodContracts/step1/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add first method (step 2)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methodContracts/step2/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add more methods (step 3)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methodContracts/step3/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add remove methods and add new once (step 4)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methodContracts/step4/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }

   /**
    * Tests in particular methods.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testMethods() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject project = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         // Test empty project (step 0)
         project = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testMethods", true, true, false, 1, true, true);
         assertProjectShown(tree, project);
         IFolder srcFolder = project.getFolder("src");
         assertTrue(srcFolder.exists());
         // Add empty classes in different packages (step 1)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methods/step1/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add first method (step 2)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methods/step2/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add more methods (step 3)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methods/step3/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
         // Add remove methods and add new once (step 4)
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/verificationStatusView/methods/step4/test", srcFolder, true);
         KeY4EclipseResourcesTestUtil.build(project);
         assertProjectShown(tree, project);
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (project != null) {
            project.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(project);
         }
      }
   }
   
   /**
    * Ensures that the correct projects are shown with and without linking.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testShownContentWithAndWithoutLinking() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject generalProject = null;
      IProject firstKeyProject = null;
      IJavaProject javaProject = null;
      IProject secondKeyProject = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationStatusView.VIEW_ID);
         view = bot.viewById(VerificationStatusView.VIEW_ID);
         SWTBotTree tree = view.bot().tree();
         assertProjectShown(tree);
         // Create general project not to be shown
         generalProject = TestUtilsUtil.createProject("SWTBotVerificationStatusViewTest_testShownContentWithAndWithoutLinking_general");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", generalProject);
         KeY4EclipseResourcesTestUtil.build(generalProject);
         assertProjectShown(tree);
         // Create first key project to show
         firstKeyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testShownContentWithAndWithoutLinking_key1", true, true, false, 1, true, true);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", firstKeyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         assertProjectShown(tree, firstKeyProject);
         // Create java project not to be shown
         javaProject = TestUtilsUtil.createJavaProject("SWTBotVerificationStatusViewTest_testShownContentWithAndWithoutLinking_java");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", javaProject.getProject().getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(javaProject.getProject());
         assertProjectShown(tree, firstKeyProject);
         // Create second key project to show
         secondKeyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationStatusViewTest_testShownContentWithAndWithoutLinking_key2", true, true, false, 1, true, true);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", secondKeyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         // Open editors
         final IFile firstFile = firstKeyProject.getFile(new Path("src/myPackage/MyClass.java"));
         IEditorPart firstEditorPart = TestUtilsUtil.openEditor(firstFile);
         SWTBotEditor firstEditor = bot.activeEditor();
         assertSame(firstEditorPart, firstEditor.getReference().getEditor(false));
         final IFile secondFile = secondKeyProject.getFile(new Path("src/myPackage/MyClass.java"));
         IEditorPart secondEditorPart = TestUtilsUtil.openEditor(secondFile);
         SWTBotEditor secondEditor = bot.activeEditor();
         assertSame(secondEditorPart, secondEditor.getReference().getEditor(false));
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         // Get project explorer
         SWTBotView projectExplorer = TestUtilsUtil.getProjectExplorer(bot);
         // Enable linking
         view.toolbarToggleButton("Link with Editor/View").click();
         // Switch between editors and project explorer with linking
         firstEditor.show();
         assertSelection(tree, firstFile);
         assertProjectShown(tree, firstKeyProject);
         secondEditor.show();
         assertSelection(tree, secondFile);
         assertProjectShown(tree, secondKeyProject);
         // Select different content in project explorer
         projectExplorer.show();
         TestUtilsUtil.selectAndReveal(firstFile);
         assertSelection(tree, firstFile);
         assertProjectShown(tree, firstKeyProject);
         TestUtilsUtil.selectAndReveal(secondFile);
         assertSelection(tree, secondFile);
         assertProjectShown(tree, secondKeyProject);
         // Disable linking
         view.toolbarToggleButton("Link with Editor/View").click();
         // Switch between editors and project explorer without linking
         projectExplorer.show();
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         firstEditor.show();
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         secondEditor.show();
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         projectExplorer.show();
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         // Select different content in project explorer
         TestUtilsUtil.selectAndReveal(firstFile);
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
         TestUtilsUtil.selectAndReveal(secondFile);
         assertProjectShown(tree, firstKeyProject, secondKeyProject);
      }
      finally {
         bot.closeAllEditors();
         if (view != null) {
            view.close();
         }
         if (generalProject != null) {
            generalProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(generalProject);
         }
         if (firstKeyProject != null) {
            firstKeyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         }
         if (javaProject != null) {
            javaProject.getProject().delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(javaProject.getProject());
         }
         if (secondKeyProject != null) {
            secondKeyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         }
      }
   }
   
   /**
    * Ensures the correct selection.
    * @param tree The {@link SWTBotTree} to test.
    * @param resource The expected selected {@link IResource}.
    * @throws Exception Occurred exception.
    */
   protected void assertSelection(SWTBotTree tree, IResource resource) throws Exception {
      Object[] objects = TestUtilsUtil.getSelectedObjects(tree);
      assertNotNull(objects);
      assertEquals(1, objects.length);
      ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(resource.getProject());
      Set<Object> modelElements = projectInfo.getModelElements(resource);
      assertNotNull(modelElements);
      assertEquals(2, modelElements.size()); // The class and the default constructor.
      assertTrue(modelElements.contains(objects[0]));
   }

   /**
    * Ensures that the given {@link IProject}s are shown.
    * @param tree The {@link SWTBotTree} to test.
    * @param projects The expected shown {@link IProject}s.
    */
   protected void assertProjectShown(SWTBotTree tree, IProject... projects) {
      assertProjectShown(tree, null, projects);
   }

   /**
    * Ensures that the given {@link IProject}s are shown.
    * @param tree The {@link SWTBotTree} to test.
    * @param projects The expected shown {@link IProject}s.
    */
   protected void assertProjectShown(SWTBotTree tree, Map<Object, RGB> colorMapping, IProject... projects) {
      SWTBotTreeItem[] rootItems = tree.getAllItems();
      assertEquals(projects.length, rootItems.length);
      for (int i = 0; i < projects.length; i++) {
         assertProject(rootItems[i], projects[i], colorMapping);
      }
   }
   
   /**
    * Ensures that the correct content of the given {@link IProject} is shown.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param project The expected content.
    */
   protected void assertProject(SWTBotTreeItem item, IProject project, Map<Object, RGB> colorMapping) {
      makeVisible(item);
      assertEquals(TestUtilsUtil.getTreeItemData(item), project);
      ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
      assertNotNull(projectInfo);
      assertEquals(project, projectInfo.getProject());
      assertEquals(item.getText(), project.getName());
      item.expand();
      SWTBotTreeItem[] packageItems = item.getItems();
      PackageInfo[] packageInfos = projectInfo.getPackages();
      assertEquals(packageItems.length, packageInfos.length);
      for (int i = 0; i < packageItems.length; i++) {
         assertPackage(packageItems[i], packageInfos[i], colorMapping);
      }
      assertColor(item, colorMapping);
   }

   /**
    * Ensures that the correct content of the given {@link PackageInfo} is shown.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param project The expected content.
    */
   protected void assertPackage(SWTBotTreeItem item, PackageInfo packageInfo, Map<Object, RGB> colorMapping) {
      makeVisible(item);
      assertEquals(TestUtilsUtil.getTreeItemData(item), packageInfo);
      assertEquals(item.getText(), packageInfo.getName());
      item.expand();
      SWTBotTreeItem[] typeItems = item.getItems();
      TypeInfo[] typeInfos = packageInfo.getTypes();
      assertEquals(typeItems.length, typeInfos.length);
      for (int i = 0; i < typeItems.length; i++) {
         assertType(typeItems[i], typeInfos[i], colorMapping);
      }
      assertColor(item, colorMapping);
   }

   /**
    * Ensures that the correct content of the given {@link TypeInfo} is shown.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param project The expected content.
    */
   protected void assertType(SWTBotTreeItem item, TypeInfo typeInfo, Map<Object, RGB> colorMapping) {
      makeVisible(item);
      assertEquals(TestUtilsUtil.getTreeItemData(item), typeInfo);
      assertEquals(item.getText(), typeInfo.getName());
      item.expand();
      SWTBotTreeItem[] contentItems = item.getItems();
      MethodInfo[] methodInfos = typeInfo.getMethods();
      ObserverFunctionInfo[] observerFunctionInfos = typeInfo.getObserverFunctions();
      TypeInfo[] typeInfos = typeInfo.getTypes();
      assertEquals(contentItems.length, methodInfos.length + observerFunctionInfos.length + typeInfos.length);
      for (int i = 0; i < methodInfos.length; i++) {
         assertMethod(contentItems[i], methodInfos[i], colorMapping);
      }
      for (int i = 0; i < observerFunctionInfos.length; i++) {
         assertObserverFunction(contentItems[methodInfos.length + i], observerFunctionInfos[i], colorMapping);
      }
      for (int i = 0; i < typeInfos.length; i++) {
         assertType(contentItems[methodInfos.length + observerFunctionInfos.length + i], typeInfos[i], colorMapping);
      }
      assertColor(item, colorMapping);
   }

   /**
    * Ensures that the correct content of the given {@link MethodInfo} is shown.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param project The expected content.
    */
   protected void assertMethod(SWTBotTreeItem item, MethodInfo methodInfo, Map<Object, RGB> colorMapping) {
      makeVisible(item);
      assertEquals(TestUtilsUtil.getTreeItemData(item), methodInfo);
      assertEquals(item.getText(), methodInfo.getDisplayName());
      item.expand();
      SWTBotTreeItem[] contractItems = item.getItems();
      ContractInfo[] contractInfos = methodInfo.getContracts();
      assertEquals(contractItems.length, contractInfos.length);
      for (int i = 0; i < contractItems.length; i++) {
         assertContract(contractItems[i], contractInfos[i], colorMapping);
      }
      assertColor(item, colorMapping);
   }

   /**
    * Ensures that the correct content of the given {@link ObserverFunctionInfo} is shown.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param project The expected content.
    */
   protected void assertObserverFunction(SWTBotTreeItem item, ObserverFunctionInfo observerFunctionInfo, Map<Object, RGB> colorMapping) {
      makeVisible(item);
      assertEquals(TestUtilsUtil.getTreeItemData(item), observerFunctionInfo);
      assertEquals(item.getText(), observerFunctionInfo.getDisplayName());
      item.expand();
      SWTBotTreeItem[] contractItems = item.getItems();
      ContractInfo[] contractInfos = observerFunctionInfo.getContracts();
      assertEquals(contractItems.length, contractInfos.length);
      for (int i = 0; i < contractItems.length; i++) {
         assertContract(contractItems[i], contractInfos[i], colorMapping);
      }
      assertColor(item, colorMapping);
   }

   /**
    * Ensures that the correct content of the given {@link ContractInfo} is shown.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param project The expected content.
    */
   protected void assertContract(SWTBotTreeItem item, ContractInfo contractInfo, Map<Object, RGB> colorMapping) {
      makeVisible(item);
      assertEquals(TestUtilsUtil.getTreeItemData(item), contractInfo);
      assertEquals(item.getText(), contractInfo.getName());
      assertColor(item, colorMapping);
   }

   /**
    * Ensures that the {@link SWTBotTreeItem} has the specified {@link Color}.
    * @param item The {@link SWTBotTreeItem} to test.
    * @param colorMapping The specified {@link Color}s.
    */
   protected void assertColor(SWTBotTreeItem item, Map<Object, RGB> colorMapping) {
      if (colorMapping != null) {
         RGB rgb = colorMapping.get(TestUtilsUtil.getTreeItemData(item));
         if (rgb != null) {
            Color color = TestUtilsUtil.getForeground(item);
            assertNotNull(color);
            assertEquals(rgb, color.getRGB());
         }
      }
   }

   /**
    * Makes the given {@link SWTBotTreeItem} visible.
    * @param item The {@link SWTBotTreeItem} to become visible.
    */
   protected void makeVisible(SWTBotTreeItem item) {
      item.select();
   }
}
