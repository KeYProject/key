package org.key_project.keyide.ui.handlers;

import java.io.File;
import java.util.List;

import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.provider.ImmutableCollectionContentProvider;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.keyide.ui.visualization.VisualizationUtil;
import org.key_project.keyide.ui.dialog.ContractSelectionDialog;
import org.key_project.keyide.ui.storage.StringInput;
import org.key_project.keyide.ui.storage.StringStorage;
import org.key_project.keyide.ui.util.LogUtil;

import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.jdt.JDTUtil;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.ui.UserInterface;

import org.key_project.keyide.ui.util.KeyUtil;

@SuppressWarnings({ "restriction" })
public class StartProofHandler extends AbstractSaveExecutionHandler {
   /**
    * Last loaded {@link InitConfig}.
    */
   private InitConfig initConfig;
   
   /**
    * Defines the existing contract to use.
    */
   private Text existingContractText;
   
   



   @SuppressWarnings("static-access")
   protected Object doExecute(ExecutionEvent event) throws Exception {
      
      
       ISelection selection = HandlerUtil.getCurrentSelection(event);
       if (selection instanceof IStructuredSelection) {
           Object[] elements = ((IStructuredSelection)selection).toArray();
           for (Object element : elements) {
               if (element instanceof IMethod) {
                browseContract((IMethod)element);
               }
           }
       }
       else if (selection instanceof ITextSelection) {
           ITextSelection textSelection = (ITextSelection)selection;
           IEditorPart editor = HandlerUtil.getActiveEditor(event);
           if (editor instanceof JavaEditor) {
               JavaEditor javaEditor = (JavaEditor)editor;
               IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, textSelection);
               if (element instanceof IMethod) {
                  browseContract((IMethod)element);
               }
           }
       }
       
       
       
       
       
       VisualizationUtil visual = new VisualizationUtil();
       if(visual.shouldSwitchToKeyPerspective(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage())){
         WorkbenchUtil.openPerspective("org.key_project.keyide.ui.perspectives");
          }
       
       return null;
   }
   

   
   
   
   
   
   
   
   /**
    * Opens a dialog to select a contract for the specified method.
    */
   public void browseContract(final IMethod method) {
         try {
           if (method != null && method.exists()) {
               final IProject project = method.getResource().getProject();
               final File location = ResourceUtil.getLocation(project);
               final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
               final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
               // Load location
              

                 new AbstractKeYMainWindowJob("Test") { // A Job which does something with KeY
                    
                    @SuppressWarnings("static-access")
                  @Override
                    protected IStatus run(IProgressMonitor monitor) {
                       try {
                          if (initConfig == null) {
                          monitor.beginTask("Test", 1);// IProgressMonitor.UNKNOWN
                          
                             initConfig = KeYUtil.internalLoad(location, classPaths, bootClassPath, false);
                             
                             project.getName();}
                             if (initConfig != null) {
                                // Get method to proof in KeY
                                final IProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
                                
                                if (pm != null) {
                                    KeYJavaType type = pm.getContainerType();
                                    final ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
                                    // Open selection dialog
                                    final Services services = initConfig.getServices();
                                    final Display display = Display.getDefault();
                                    display.getDefault().asyncExec(new Runnable() {
                                       public void run() {
                                          Shell shell = new Shell(display);
                                          Shell dialogShell = new Shell(shell, SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);
                                          ContractSelectionDialog dialog = new ContractSelectionDialog(dialogShell, ImmutableCollectionContentProvider.getInstance(), services);
                                          dialog.setTitle("Contract selection");
                                          dialog.setMessage("Select a contract to debug.");
                                          dialog.setInput(operationContracts);
                                          existingContractText=new Text(dialogShell, SWT.TOP);
                                          FunctionalOperationContract selectedContract = KeyUtil.findContract(operationContracts, getContractId());
                                          if (selectedContract != null) {
                                              dialog.setInitialSelections(new Object[] {selectedContract});
                                          }
                                          if (dialog.open() == ContractSelectionDialog.OK) {
                                              Object result = dialog.getFirstResult();
                                              if (result instanceof FunctionalOperationContract) {
                                                  FunctionalOperationContract foc = (FunctionalOperationContract)result;
                                                  existingContractText.setText(foc.getName());
                                                  KeYMediator mediator = MainWindow.getInstance().getMediator();
                                                  //MainWindow.setVisibleMode(false);
                                                  MainWindow.getInstance().setVisibleMode(false);
                                                  findOrStartProof(foc.createProofObl(initConfig, foc), initConfig, mediator);
                                                  
                                                  
                                                  
                                                  //openeditor
                                                  String inputText = NonGoalInfoView.computeText(mediator, mediator.getSelectedProof().root());
                                                  String inputSequent=(String) inputText.subSequence(0, inputText.length()-12);
                                                  IStorage storage = new StringStorage(inputSequent, pm.getName());
                                                  IStorageEditorInput input = new StringInput(storage);
                                                  try {
                                                   PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().openEditor(input, "org.key_project.keyide.ui.editor");
                                                }
                                                catch (PartInitException e) {
                                                   // TODO Auto-generated catch block
                                                   e.printStackTrace();
                                                }
                                                 
                                                  
                                                  
                                                  
                                                  
                                                  
                                                
                                              }
                                          }
                                      }
                                  });
                                    
                                }
                                else {
                                    throw new IllegalStateException("Can't find method \"" + JDTUtil.getQualifiedMethodLabel(method) + "\" in KeY.");
                                }
                            }
                             
                          SWTUtil.checkCanceled(monitor);
                          monitor.worked(1);
                          monitor.done();
                          this.done(Status.OK_STATUS);
                          return Status.OK_STATUS;                          
                       }
                       catch (OperationCanceledException e) {
                          return Status.CANCEL_STATUS;
                       }
                     catch (Exception e) {
                        LogUtil.getLogger().logError(e);
                        LogUtil.getLogger().openErrorDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), e);
                        return Status.CANCEL_STATUS;
                     }
                    }                   
                 }.schedule();    
               }
           
       }
       catch (Exception e) {
           LogUtil.getLogger().logError(e);
           LogUtil.getLogger().openErrorDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), e);
       }
   }

   
   
   
   /**
    * Returns the ID of the existing contract.
    * @return The ID of the existing contract.
    */
   protected String getContractId() {
       return existingContractText.getText();
   }

   

   
   private void findOrStartProof(ProofOblInput po, InitConfig initConfig, KeYMediator mediator) {
      Proof proof = findPreferablyClosedProof(po, initConfig);
      if(proof == null) {
       UserInterface ui = mediator.getUI();
          ProblemInitializer pi = 
                new ProblemInitializer(ui, mediator.getProfile(), initConfig.getServices(), true, ui);
          try {
              pi.startProver(initConfig, po, 0);
          } catch(ProofInputException exc) {
       ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
          }
      } else {
          mediator.setProof(proof);
      }
  }
   
   
   private Proof findPreferablyClosedProof(ProofOblInput po,  InitConfig initConfig) {
      ImmutableSet<Proof> proofs = initConfig.getServices().getSpecificationRepository().getProofs(po);
      
      //no proofs?
      if(proofs.size() == 0) {
          return null;
      }
      
      //try to find closed proof
      for(Proof proof : proofs) {
          if(proof.mgt().getStatus().getProofClosed()) {
              return proof;
          }
      }
      
      //just take any proof
      return proofs.iterator().next();
  }    
  
   
   
   
   
   
   
}
 