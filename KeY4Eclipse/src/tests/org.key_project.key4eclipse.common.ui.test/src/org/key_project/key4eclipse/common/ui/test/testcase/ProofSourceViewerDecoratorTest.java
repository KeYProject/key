package org.key_project.key4eclipse.common.ui.test.testcase;

import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.util.ArrayList;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.resource.FontDescriptor;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
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
import de.uka.ilkd.key.proof.Node;
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
   private Color lightblueColor = new Color(null,167,210,210);
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
      Font boldFont = null;
      try {
         shell.setText("ProofSourceViewerDecoratorTest");
         shell.setSize(600, 400);
         shell.setLayout(new FillLayout());
         // let showNode fill StyleRanges of StyledText
         ISourceViewer sourceViewer = new SourceViewer(shell, null, SWT.NONE);
         ProofSourceViewerDecorator decorator = new ProofSourceViewerDecorator(sourceViewer);
         decorator.showNode(new Node(proof), SymbolicExecutionUtil.createNotationInfo(proof));
         StyledText text = sourceViewer.getTextWidget();
         
         // fill Array for Test with correct StyleRanges
         FontDescriptor descriptor = FontDescriptor.createFrom(sourceViewer.getTextWidget().getFont()).setStyle(SWT.BOLD); 
         boldFont = descriptor.createFont(sourceViewer.getTextWidget().getDisplay());
         ArrayList<StyleRange> shouldRanges = new ArrayList<StyleRange>();
         StyleRange keyKeywords = new StyleRange();
         keyKeywords.foreground = blueColor;
         keyKeywords.font = boldFont;
         keyKeywords.start = 12;
         keyKeywords.length = 10;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 35;
         keyKeywords.length = 1;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 59;
         keyKeywords.length = 9;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 71;
         keyKeywords.length = 4;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 101;
         keyKeywords.length = 13;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 123;
         keyKeywords.length = 4;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 134;
         keyKeywords.length = 15;
         shouldRanges.add(keyKeywords);
         StyleRange update = new StyleRange();
         update.background = lightblueColor;
         update.start = 154;
         update.length = 17;
         shouldRanges.add(update);
         StyleRange javaKeywords = new StyleRange();
         javaKeywords.foreground = purpleColor;
         javaKeywords.font = boldFont;
         javaKeywords.start = 198;
         javaKeywords.length = 4;
         shouldRanges.add(javaKeywords);
         javaKeywords.start = 203;
         javaKeywords.length = 3;
         shouldRanges.add(javaKeywords);
         javaKeywords.start = 280;
         javaKeywords.length = 5;
         shouldRanges.add(javaKeywords);
         keyKeywords.start = 426;
         keyKeywords.length = 7;
         shouldRanges.add(keyKeywords);
         keyKeywords.start = 461;
         keyKeywords.length = 7;
         shouldRanges.add(keyKeywords);
         // check if StyleRanges are the same
         for (int i = 0; i < shouldRanges.size(); i++) {
            assert (shouldRanges.get(i).equals(text.getStyleRanges()[i]));
         }
      
      } finally {
         shell.setVisible(false);
         shell.dispose();
         purpleColor.dispose();
         if (boldFont != null) {
            boldFont.dispose();
         }
         blueColor.dispose();
         lightblueColor.dispose();
   }
  
      
   }
}
