/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISourcePathProvider;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.ui.visualization.launch.SETFileSourceLookupDirector;
import org.key_project.sed.ui.visualization.launch.SETFileSourceLookupParticipant;
import org.key_project.sed.ui.visualization.launch.SETFileSourcePathComputerDelegate;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests the source code lookup in launched SET files. This involves in particular
 * {@link SETFileSourceLookupDirector},
 * {@link SETFileSourceLookupParticipant} and
 * {@link SETFileSourcePathComputerDelegate}.
 * @author Martin Hentschel
 */
public class SWTBotSetFileSourceLookupTest extends AbstractSWTBotSetFileTest {
   /**
    * Launches "data/Number/test/Number.set".
    */
   @Test
   public void testStatementSourceLocation() throws Exception {
      ISetFileTestSteps steps = new ISetFileTestSteps() {
         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            // Select statement in debug tree
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1, 0, 0, 0);
            // Get statement that should be selected in opened editor.
            ISEDStatement statement = (ISEDStatement)TestUtilsUtil.getTreeItemData(item);
            // Make sure that an editor is opened
            SWTBotEditor editor = TestUtilsUtil.waitForEditor(bot);
            assertNotNull(editor);
            assertEquals(1, bot.editors().size());
            // Make sure that the correct editor is opened
            assertTrue(statement instanceof ISourcePathProvider);
            String location = ((ISourcePathProvider)statement).getSourcePath();
            assertNotNull(location);
            File locationFile = new File(location);
            assertTrue(locationFile.exists());
            IEditorPart editorPart = editor.getReference().getEditor(true);
            TestSedCoreUtil.assertDebugEditor(editorPart, locationFile, target, statement);
            // Make sure that the correct line is annotated in the editor
            TestSedCoreUtil.assertDebugCodeAnnotation(editorPart, statement);
            // Close editor
            editor.close();
         }
      };
      doSetFileTest("SWTBotSetFileSourceLookupTest_testStatementSourceLocation", 
                    "data/Number/test", 
                    "Number.set",
                    steps,
                    new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\Number.java", "Number.java"));
   }
}