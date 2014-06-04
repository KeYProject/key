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

package org.key_project.sed.key.core.test.testcase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.internal.ui.javaeditor.ASTProvider;
import org.junit.Test;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.util.ASTNodeByEndIndexSearcher;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests {@link ASTNodeByEndIndexSearcher}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class ASTNodeByEndIndexSearcherTest extends AbstractSetupTestCase {
   /**
    * Tests the search result of the search process via
    * {@link ASTNodeByEndIndexSearcher#search(org.eclipse.jdt.core.dom.ASTNode, int)}.
    */
   @Test
   public void testSearch() throws CoreException, InterruptedException {
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("ASTNodeByEndIndexSearcherTest_testSearchResult");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/simpleIf/test", project.getProject().getFolder("src"));
      // Get method
      IMethod method = TestUtilsUtil.getJdtMethod(project, "SimpleIf", "min", "I", "I");
      assertNotNull(method);
      // Create AST
      IJavaElement element = JavaCore.create(method.getResource());
      assertTrue(element instanceof ICompilationUnit);
      ASTParser parser = ASTParser.newParser(ASTProvider.SHARED_AST_LEVEL);
      parser.setSource((ICompilationUnit)element);
      ASTNode root = parser.createAST(null);
      // Search method
      ASTNode methodNode = ASTNodeByEndIndexSearcher.search(root, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
      assertNotNull(methodNode);
      assertTrue(methodNode instanceof MethodDeclaration);
      assertEquals(method.getElementName(), ((MethodDeclaration)methodNode).getName().toString());
      assertEquals(method.getSourceRange().getOffset() + method.getSourceRange().getLength(), methodNode.getStartPosition() + methodNode.getLength());
      // Test not existing end index
      ASTNode nullNode = ASTNodeByEndIndexSearcher.search(root, method.getSourceRange().getOffset() + method.getSourceRange().getLength() - 1);
      assertNull(nullNode);
      // Test invalid index
      nullNode = ASTNodeByEndIndexSearcher.search(root, -1);
      assertNull(nullNode);
      // Test invalid root
      nullNode = ASTNodeByEndIndexSearcher.search(null, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
      assertNull(nullNode);
   }
}