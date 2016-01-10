package org.key_project.key4eclipse.common.ui.test.testcase;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.ArrayList;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Shell;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.ui.test.util.TestKeYUIUtil;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Tests for ProofSourceViewerDecorator.
 * @author Anna Marie Filighera
 *
 */
public class ProofSourceViewerDecoratorTest {
   /**
    * {@link Color} used for highlighting KeY keywords.
    */
   private Color blueColor = new Color(null, 0, 0, 192);
   /**
    * {@link Color} used for java keywords.
    */
   private Color purpleColor = new Color(null, 127, 0, 85);
   /**
    * {@link Color} used for highlighting updates.
    */
   private Color lightblueColor = new Color(null, 167, 210, 210);
   /**
    * Test for Syntaxhighlighting.
    * @throws Exception
    */
   @Test
   public void testSyntaxHighlighting() throws Exception {
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("ProofSourceViewerDecoratorTest_testSyntaxHighlighting");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
      // Get local file in operating system of folder src 
      File location = ResourceUtil.getLocation(src);
      // Load source code in KeY and get contract to proof which is the first contract of LogRecord#getBalance().
      KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(location, null, null, null);
      IProgramMethod pm = TestKeYUIUtil.searchProgramMethod(environment.getServices(), "LogRecord", "getBalance");
      ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
      FunctionalOperationContract foc = CollectionUtil.getFirst(operationContracts);
      Proof proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc));
      assertNotNull(proof);
      Shell shell = new Shell();
      try {
         shell.setText("ProofSourceViewerDecoratorTest");
         shell.setSize(600, 400);
         shell.setLayout(new FillLayout());
         // let showNode fill StyleRanges of StyledText
         ISourceViewer sourceViewer = new SourceViewer(shell, null, SWT.NONE);
         ProofSourceViewerDecorator decorator = new ProofSourceViewerDecorator(sourceViewer);
         decorator.showNode(proof.root(), SymbolicExecutionUtil.createNotationInfo(proof));
         StyledText text = sourceViewer.getTextWidget();
         
         // fill Array for Test with correct StyleRanges
         ArrayList<StyleRange> shouldRanges = new ArrayList<StyleRange>();
         StyleRange keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 12;
         keyKeywords.length = 10;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 33;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 35;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 52;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 59;
         keyKeywords.length = 9;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 71;
         keyKeywords.length = 4;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 80;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 93;
         keyKeywords.length = 13;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 115;
         keyKeywords.length = 4;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 124;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 126;
         keyKeywords.length = 15;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 146;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 153;
         keyKeywords.length = 5;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 160;
         keyKeywords.length = 2;
         shouldRanges.add(keyKeywords);
         StyleRange update = new StyleRange();
         update.background = lightblueColor;
         update.start = 163;
         update.length = 17;
         shouldRanges.add(update);
         StyleRange javaKeywords = new StyleRange();
         javaKeywords.foreground = purpleColor;
         javaKeywords.fontStyle = SWT.BOLD;
         javaKeywords.start = 205;
         javaKeywords.length = 4;
         shouldRanges.add(javaKeywords);
         javaKeywords = new StyleRange();
         javaKeywords.foreground = purpleColor;
         javaKeywords.fontStyle = SWT.BOLD;
         javaKeywords.start = 210;
         javaKeywords.length = 3;
         shouldRanges.add(javaKeywords);
         javaKeywords = new StyleRange();
         javaKeywords.foreground = purpleColor;
         javaKeywords.fontStyle = SWT.BOLD;
         javaKeywords.start = 277;
         javaKeywords.length = 5;
         shouldRanges.add(javaKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 390;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 397;
         keyKeywords.length = 5;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 416;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 442;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 444;
         keyKeywords.length = 7;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 478;
         keyKeywords.length = 7;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 530;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 562;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 564;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 567;
         keyKeywords.length = 9;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 589;
         keyKeywords.length = 4;
         shouldRanges.add(keyKeywords);
         keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.fontStyle = SWT.BOLD;
         keyKeywords.start = 614;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         // check if StyleRanges are the same
         StyleRange[] isRanges = text.getStyleRanges();
         assertTrue ("The amount of highlights marked is not correct.", shouldRanges.size() == isRanges.length);
         for (int i = 0; i < shouldRanges.size(); i++) {
            assertTrue ("Mark Nr. "+ i + " is not correct.", shouldRanges.get(i).equals(isRanges[i]));
         }
      
      } finally {
         shell.setVisible(false);
         shell.dispose();
         purpleColor.dispose();
         blueColor.dispose();
         lightblueColor.dispose();
   }
  
      
   }
}
