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

package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.SearchAnnotation;
import org.key_project.sed.core.annotation.impl.SearchAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.sed.key.core.model.KeYStatement;

/**
 * Ensures that {@link ISEAnnotationLink}s are automatically added to new nodes.
 * @author Martin Hentschel
 */
public class SWTBotInitialAnnotationLinkTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Ensures that initial search {@link ISEAnnotationLink}s are added to new {@link ISENode}s
    * (more precise: only {@link KeYStatement}s are tested).
    */
   @Test
   public void testInitialSearchAnnotations() throws Exception {
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDebugTarget target, ILaunch launch) throws Exception {
            // Add search annotation
            ISEAnnotationType type = SEAnnotationUtil.getAnnotationtype(SearchAnnotationType.TYPE_ID);
            SearchAnnotation annotation = (SearchAnnotation)type.createAnnotation();
            annotation.setSearch("=");
            target.registerAnnotation(annotation);
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0); // Select thread
            resume(bot, item, target);
            // Test annotation
            ISEAnnotationLink[] links = annotation.getLinks();
            assertEquals(3, links.length);
         }
      };
      doKeYDebugTargetTest("SWTBotInitialAnnotationLinkTest_testInitialSearchAnnotations", 
                           "data/statements/test", 
                           true,
                           true,
                           createMethodSelector("FlatSteps", "doSomething", "I", "QString;", "Z"), 
                           null,
                           null,
                           Boolean.FALSE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE, 
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.TRUE,
                           Boolean.FALSE,
                           14, 
                           executor);
   }
}