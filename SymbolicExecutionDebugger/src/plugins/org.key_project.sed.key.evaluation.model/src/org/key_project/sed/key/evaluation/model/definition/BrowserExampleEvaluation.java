package org.key_project.sed.key.evaluation.model.definition;

import java.net.URL;
import java.util.Collections;
import java.util.List;

import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.browser.IWebBrowser;
import org.eclipse.ui.browser.IWorkbenchBrowserSupport;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.tooling.AbstractWorkbenchModifier;
import org.key_project.sed.key.evaluation.model.util.EvaluationModelImages;
import org.key_project.sed.key.evaluation.model.validation.NotUndefinedValueValidator;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;

public class BrowserExampleEvaluation extends AbstractEvaluation {
   /**
    * The only instance of this class.
    */
   public static final BrowserExampleEvaluation INSTANCE = new BrowserExampleEvaluation();

   /**
    * The default {@link EvaluationInput} of {@link #INSTANCE}.
    */
   public static EvaluationInput INSTANCE_INPUT = new EvaluationInput(INSTANCE);
   
   /**
    * The name of the browser tool.
    */
   public static final String BROWSER_NAME = "browser";
   
   static {
      RandomFormInput rfi = (RandomFormInput) INSTANCE_INPUT.getFormInputs()[0];
      AbstractPageInput<?> questionInput = rfi.getPageInput(1);
      rfi.setCurrentPageInput(questionInput);
      rfi.setPageOrder(CollectionUtil.toList(rfi.getPageInputs()));
      rfi.setTool(questionInput, INSTANCE.getTool(BROWSER_NAME));
   }
   
   private BrowserExampleEvaluation() {
      super("Browser Evaluation", null);
   }

   @Override
   protected List<AbstractForm> computeForms() {
      String urlQuestion = "Which website is opened?";
      String buttonsQuestion = "Which toolbar buttons are enabled?";
      String protocolQuestion = "Which protocol is used?";
      RadioButtonsQuestion protocolSubQuestion = new RadioButtonsQuestion("protocolQuestions", protocolQuestion, true, null, new NotUndefinedValueValidator("Question '" + protocolQuestion + "' not answered."), true, new Choice("ftp", "ftp"), new Choice("http", "http"), new Choice("pop3", "pop3"));
      QuestionPage questionPage = new QuestionPage("questionPage", 
                                                   "Browser", 
                                                   "Please answer the questions to the best of your knowledge.",
                                                   false,
                                                   false,
                                                   new AbstractWorkbenchModifier() {
                                                      private IWebBrowser browser;
        
                                                      private Display display;
                                                      
                                                      @Override
                                                      public String modifyWorkbench() throws Exception {
                                                         IRunnableWithException run = new AbstractRunnableWithException() {
                                                            @Override
                                                            public void run() {
                                                               try {
                                                                  IWorkbenchBrowserSupport support = PlatformUI.getWorkbench().getBrowserSupport();
                                                                  browser = support.createBrowser(IWorkbenchBrowserSupport.LOCATION_BAR | IWorkbenchBrowserSupport.NAVIGATION_BAR | IWorkbenchBrowserSupport.AS_EDITOR, null, null, null);
                                                                  browser.openURL(new URL("http://key-project.org"));
                                                                  IWorkbenchPage page = WorkbenchUtil.getActivePage();
                                                                  page.toggleZoom(page.getActivePartReference());
                                                               }
                                                               catch (Exception e) {
                                                                  setException(e);
                                                               }
                                                            }
                                                         };
                                                         display = getShell().getDisplay();
                                                         display.syncExec(run);
                                                         if (run.getException() != null) {
                                                            throw run.getException();
                                                         }
                                                         return null;
                                                      }
                                                      
                                                      @Override
                                                      public void cleanWorkbench() throws Exception {
                                                         display.syncExec(new Runnable() {
                                                            @Override
                                                            public void run() {
                                                               if (browser != null) {
                                                                  browser.close();
                                                               }
                                                            }
                                                         });
                                                      }
                                                   },
                                                   new RadioButtonsQuestion("url", urlQuestion, true, null, new NotUndefinedValueValidator("Question '" + urlQuestion + "' not answered."), true, new Choice("http://www.se.tu-darmstadt.de", "se"), new Choice("http://key-project.org", "key", protocolSubQuestion)),
                                                   new CheckboxQuestion("buttons", buttonsQuestion, true, null, new NotUndefinedValueValidator("Question '" + buttonsQuestion + "' not answered."), true, new Choice("Back", "Back"), new Choice("Forward", "Forward"), new Choice("Stop", "Stop"), new Choice("Refresh", "Refresh")));
      SendFormPage sendFixedPage = new SendFormPage("sendFixedPage", "sendFixedPageTitle", "sendFixedPageMessage", "additionalDataCollectedByServer");
      RandomForm form = new RandomForm("form", false, new ToolPage(getTool(BROWSER_NAME), null, false), questionPage, sendFixedPage);
      return Collections.<AbstractForm>singletonList(form);
   }

   @Override
   protected List<Tool> computeTools() {
      Tool browser = new Tool(BROWSER_NAME, null, null, isUIAvailable() ? EvaluationModelImages.getImage(EvaluationModelImages.BROWSER) : null);
      return CollectionUtil.toList(browser);
   }
}
