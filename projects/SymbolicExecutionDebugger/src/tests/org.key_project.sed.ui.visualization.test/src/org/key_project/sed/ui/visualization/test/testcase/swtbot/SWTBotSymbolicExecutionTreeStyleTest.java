package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.annotation.impl.CommentAnnotationType;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;

/**
 * Tests the used {@link Style}s in symbolic execution trees.
 * @author Martin Hentschel
 */
public class SWTBotSymbolicExecutionTreeStyleTest extends AbstractSymbolicExecutionTreeTest {
   /**
    * Launches "data/Number/test/Number.set" and changes the foreground color.
    */
   @Test
   public void testChangeForegroundColor() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setCustomForegroundColor(new RGB(43, 43, 43));
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testChangeForegroundColor", 
                   change, 
                   "ForegroundColorBefore", 
                   "ForegroundColorAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and changes the background color.
    */
   @Test
   public void testChangeBackgroundColor() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setCustomBackgroundColor(new RGB(43, 43, 43));
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testChangeBackgroundColor", 
                   change, 
                   "BackgroundColorBefore", 
                   "BackgroundColorAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and activates the foreground.
    */
   @Test
   public void testActivateForegroundAnnotation() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
            link.getSource().setCustomHighlightForeground(Boolean.FALSE);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setCustomHighlightForeground(Boolean.TRUE);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testActivateForegroundAnnotation", 
                   change, 
                   "ActivateForegroundBefore", 
                   "ActivateForegroundAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and deactivates the foreground.
    */
   @Test
   public void testDeactivateForegroundAnnotation() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setCustomHighlightForeground(Boolean.FALSE);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testDeactivateForegroundAnnotation", 
                   change, 
                   "DeactivateForegroundBefore", 
                   "DeactivateForegroundAfter");
   }
   
   /**
    * Launches "data/Number/test/Number.set" and activates the background.
    */
   @Test
   public void testActivateBackgroundAnnotation() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
            link.getSource().setCustomHighlightBackground(Boolean.FALSE);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setCustomHighlightBackground(Boolean.TRUE);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testActivateBackgroundAnnotation", 
                   change, 
                   "ActivateBackgroundBefore", 
                   "ActivateBackgroundAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and deactivates the background.
    */
   @Test
   public void testDeactivateBackgroundAnnotation() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setCustomHighlightBackground(Boolean.FALSE);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testDeactivateBackgroundAnnotation", 
                   change, 
                   "DeactivateBackgroundBefore", 
                   "DeactivateBackgroundAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and enables an annotation.
    */
   @Test
   public void testEnableAnnotation() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
            link.getSource().setEnabled(false);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setEnabled(true);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testEnableAnnotation", 
                   change, 
                   "EnableBefore", 
                   "EnableAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and disables an annotation.
    */
   @Test
   public void testDisableAnnotation() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getSource().setEnabled(false);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testDisableAnnotation", 
                   change, 
                   "DisableBefore", 
                   "DisableAfter");
   }

   /**
    * Launches "data/Number/test/Number.set" and removes an annotation link.
    */
   @Test
   public void testRemoveAnnotationLink() throws Exception {
      IChange change = new IChange() {
         private ISEDAnnotationLink link;
         
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link = addLinkToThread(target);
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            link.getTarget().removeAnnotationLink(link);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testRemoveAnnotationLink", 
                   change, 
                   "RemoveLinkBefore", 
                   "RemoveLinkAfter");
   }
   
   /**
    * Launches "data/Number/test/Number.set" and adds an annotation with link.
    */
   @Test
   public void testAddAnnotationLink() throws Exception {
      IChange change = new IChange() {
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
         }

         @Override
         public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            addLinkToThread(target);
         }
      };
      doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testAddAnnotationLink", 
                   change, 
                   null, 
                   "AddLink");
   }
   
   /**
    * Creates an {@link ISEDAnnotationLink} and adds it to the first {@link ISEDThread} of the given {@link ISEDDebugTarget}.
    * @param target The {@link ISEDDebugTarget} to modify.
    * @return The created {@link ISEDAnnotationLink}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDAnnotationLink addLinkToThread(ISEDDebugTarget target) throws DebugException {
      ISEDThread thread = target.getSymbolicThreads()[0];
      ISEDAnnotationType type = SEDAnnotationUtil.getAnnotationtype(CommentAnnotationType.TYPE_ID);
      ISEDAnnotation annotation = type.createAnnotation();
      annotation.setCustomBackgroundColor(new RGB(255, 0, 0));
      annotation.setCustomForegroundColor(new RGB(0, 255, 0));
      annotation.setCustomHighlightBackground(Boolean.TRUE);
      annotation.setCustomHighlightForeground(Boolean.TRUE);
      annotation.setEnabled(true);
      annotation.setId("AnnotationUniqueID");
      ISEDAnnotationLink link = type.createLink(annotation, thread);
      target.registerAnnotation(annotation);
      thread.addAnnotationLink(link);
      link.setId("AnnotationLinkUniqueID");
      return link;
   }

   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeFirstBackgroundColor()}.
    */
   @Test
   public void testFirstBackgroundColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeFirstBackgroundColor();
      try {
         IChange change = new IChange() {
            @Override
            public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            }

            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeFirstBackgroundColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testFirstBackgroundColorChange", 
                      change, 
                      null, 
                      "ChangeFirstBackgroundColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeFirstBackgroundColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeSecondBackgroundColor()}.
    */
   @Test
   public void testSecondBackgroundColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeSecondBackgroundColor();
      try {
         IChange change = new IChange() {
            @Override
            public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            }

            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeSecondBackgroundColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testSecondBackgroundColorChange", 
                      change, 
                      null, 
                      "ChangeSecondBackgroundColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeSecondBackgroundColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#isExecutionTreeNodeDirectionHorizontal()}.
    */
   @Test
   public void testDirectionChange() throws Exception {
      boolean originalValue = VisualizationPreferences.isExecutionTreeNodeDirectionHorizontal();
      try {
         IChange change = new IChange() {
            @Override
            public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            }

            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeDirectionHorizontal(false);
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testDirectionChange", 
                      change, 
                      null, 
                      "ChangeBackgroundColorDirection");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeDirectionHorizontal(originalValue);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeForegroundColor()}.
    */
   @Test
   public void testForegroundColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeForegroundColor();
      try {
         IChange change = new IChange() {
            @Override
            public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            }

            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeForegroundColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testForegroundColorChange", 
                      change, 
                      null, 
                      "ChangeForegroundColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeForegroundColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeTextColor()}.
    */
   @Test
   public void testTextColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeTextColor();
      try {
         IChange change = new IChange() {
            @Override
            public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            }

            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeTextColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testTextColorChange", 
                      change, 
                      null, 
                      "ChangeTextColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeTextColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeConnectionColor()}.
    */
   @Test
   public void testConnectionColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeConnectionColor();
      try {
         IChange change = new IChange() {
            @Override
            public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            }

            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeConnectionColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testConnectionColorChange", 
                      change, 
                      null, 
                      "ChangeConnectionColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeConnectionColor(originalColor);
      }
   }
   
   /**
    * Launches the example {@code data/Number/test/Number.set},
    * compares it with oracle, performs a change and compares it with oracle again.
    * @param projectName The name of the project to use.
    * @param change The {@link IChange} to perform.
    * @param beforeOracleSuffix The suffix of the first oracle file before the change.
    * @param afterOracleSuffix The suffix of the second oracle file after the change.
    * @throws Exception Occurred Exception.
    */
   protected void doChangeTest(String projectName,
                               final IChange change,
                               final String beforeOracleSuffix, 
                               final String afterOracleSuffix) throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {
         @Override
         public void init(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            change.init(bot, project, setFile, debugView, debugTree, launch, target);
         }

         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "Number.set", "data/Number/oracle", beforeOracleSuffix);
            change.change(bot, project, setFile, debugView, debugTree, launch, target);
            assertDiagram(bot, project, "Number.set", "data/Number/oracle", afterOracleSuffix);
         }
      };
      doDiagramTest(projectName, 
                    "data/Number/test", 
                    "Number.set", 
                    steps, 
                    new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\Number.java", "Number.java"));
   }
   
   /**
    * Performs a change during {@link SWTBotSymbolicExecutionTreeStyleTest#doChangeTest(IChange, String)}.
    * @author Martin Hentschel
    */
   protected static interface IChange {
      /**
       * Initializes the environment before the initial state is tested.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param project The {@link IProject} which contains the SET file.
       * @param setFile The SET file.
       * @param debugView The debug view.
       * @param debugTree The debug tree.
       * @param launch The {@link ILaunch}.
       * @param target The {@link ISEDDebugTarget}.
       */
      public void init(SWTWorkbenchBot bot, 
                       IProject project, 
                       IFile setFile, 
                       SWTBotView debugView, 
                       SWTBotTree debugTree, 
                       ILaunch launch, 
                       ISEDDebugTarget target) throws Exception;
      
      /**
       * Performs the change.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param project The {@link IProject} which contains the SET file.
       * @param setFile The SET file.
       * @param debugView The debug view.
       * @param debugTree The debug tree.
       * @param launch The {@link ILaunch}.
       * @param target The {@link ISEDDebugTarget}.
       */
      public void change(SWTWorkbenchBot bot, 
                         IProject project, 
                         IFile setFile, 
                         SWTBotView debugView, 
                         SWTBotTree debugTree, 
                         ILaunch launch, 
                         ISEDDebugTarget target) throws Exception;
   }
}
