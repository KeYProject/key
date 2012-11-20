package org.key_project.keyide.ui.util;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.provider.ImmutableCollectionContentProvider;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.keyide.ui.dialog.ContractSelectionDialog;
import org.key_project.keyide.ui.storage.StringInput;
import org.key_project.keyide.ui.storage.StringStorage;
import org.key_project.keyide.ui.visualization.VisualizationUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * This class provides static methods for the communication between KeY and the Eclipse UI.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */

public class KeyToUIUtil {
   
   /**
    * Last loaded {@link InitConfig}.
    */
   private static InitConfig initConfig;
   
   /**
    * Defines the existing contract to use.
    */
   private static Text existingContractText;
   
   /**
    * The {@link Proof} to currently use.
    */
   private static Proof proof = null;
   
   /**
    * The {@link UserInterface} of KeY.
    */
   private static UserInterface ui;

   
   
   /**
    * Opens a dialog to select a contract for the specified method, furthermore creates the proof for that method
    * @param method The method to create the proof for.
    */
   public static void createProof(final IMethod method) {
         try {
           if (method != null && method.exists()) {
               // Load location
               final IProject project = method.getResource().getProject();
               final File location = ResourceUtil.getLocation(project);
               final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
               final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
                 new Job("Loading Proof") { // A Job to load the proof in KeY
                  @Override
                    protected IStatus run(IProgressMonitor monitor) {
                       try {
                          if (ui==null)
                             ui = new CustomConsoleUserInterface(false);
                          if (initConfig == null) {
                             monitor.beginTask("Loading Proof", 1);
                             DefaultProblemLoader loader = ui.load(location, classPaths, bootClassPath);
                             initConfig = loader.getInitConfig();
                          }
                          if (initConfig != null) {
                             // Get method to proof in KeY
                             final IProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
                             if (pm != null) {
                                 KeYJavaType type = pm.getContainerType();
                                 final ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
                                 final Services services = initConfig.getServices();
                                 final Display display = Display.getDefault();
                                 display.asyncExec(new Runnable() {
                                    public void run() {
                                       Shell shell = new Shell(display);
                                       // Open selection dialog
                                       ContractSelectionDialog dialog = initializeDialog(operationContracts, shell, services);
                                       openDialog(dialog, operationContracts, ui);
                                       //Open proof in Editor if correctly selected
                                       if(proof!=null)
                                          KeyToUIUtil.openEditor(method.getElementName(), ui);
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
                          done(Status.OK_STATUS);
                          return Status.OK_STATUS;                          
                       }
                       catch (OperationCanceledException e) {
                          return Status.CANCEL_STATUS;
                       }
                     catch (Exception e) {
                        LogUtil.getLogger().logError(e);
                        return Status.CANCEL_STATUS;
                     }
                  }
              }.schedule();
          }
       }
       catch (Exception e) {
          LogUtil.getLogger().logError(e);
       }
   }

   /**
    * Searches a {@link FunctionalOperationContract} with the given name.
    * @param operationContracts The available {@link FunctionalOperationContract} to search in.
    * @param contractName The name of the {@link FunctionalOperationContract} to search.
    * @return The found {@link FunctionalOperationContract} or {@code null} if no one was found.
    */
   public static FunctionalOperationContract findContract(ImmutableSet<FunctionalOperationContract> operationContracts, 
                                                          final String contractName) {
       return CollectionUtil.search(operationContracts, new IFilter<FunctionalOperationContract>() {
           @Override
           public boolean select(FunctionalOperationContract element) {
               return element != null && ObjectUtil.equals(element.getName(), contractName);
           }
       });
   }
   
   
   /**
    * Returns the ID of the existing contract.
    * @return The ID of the existing contract.
    */
   protected static String getContractId() {
       return existingContractText.getText();
   }   
  
   
   
   
   /**
    * Opens the currently selected {@link Proof} into the KeY-Editor.
    * @param name The  name to display at the editor-tab
    * @param ui The UserInterface that holds the KeYMediator
    */
   public static void openEditor(final String name, final UserInterface ui){
      String inputText = NonGoalInfoView.computeText(ui.getMediator(), proof.root());
      String inputSequent=(String) inputText.subSequence(0, inputText.length()-12);
      IStorage storage = new StringStorage(inputSequent, name);
      IStorageEditorInput input = new StringInput(storage);
      try {
         PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().openEditor(input, "org.key_project.keyide.ui.editor");
      }
      catch (PartInitException e) {
         e.printStackTrace();
      }
   }
   
   
   
   /**
    * Asks the user if he wants to switch into the KeY-perspective and opens it if necessary
    */
   @SuppressWarnings("static-access")
   public static void switchPerspective() {
      VisualizationUtil visual = new VisualizationUtil();
      if(visual.shouldSwitchToKeyPerspective(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage())){
         WorkbenchUtil.openPerspective("org.key_project.keyide.ui.perspectives");
      }
      
   }
   
   
   private static ContractSelectionDialog initializeDialog(ImmutableSet<FunctionalOperationContract> operationContracts, Shell shell, Services services) {
      Shell dialogShell = new Shell(shell, SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);
      ContractSelectionDialog dialog = new ContractSelectionDialog(dialogShell, ImmutableCollectionContentProvider.getInstance(), services);
      dialog.setTitle("Contract selection");
      dialog.setMessage("Select a contract to debug.");
      dialog.setInput(operationContracts);
      existingContractText=new Text(dialogShell, SWT.TOP);
      return dialog;
   } 
   
   private static void openDialog(ContractSelectionDialog dialog, ImmutableSet<FunctionalOperationContract> operationContracts, UserInterface ui) {
      FunctionalOperationContract selectedContract = KeyToUIUtil.findContract(operationContracts, getContractId());
      if (selectedContract != null) {
          dialog.setInitialSelections(new Object[] {selectedContract});
      }
      if (dialog.open() == ContractSelectionDialog.OK) {
          Object result = dialog.getFirstResult();
          if (result instanceof FunctionalOperationContract) {
              FunctionalOperationContract foc = (FunctionalOperationContract)result;
              existingContractText.setText(foc.getName());
              try {
                proof = ui.createProof(initConfig, foc.createProofObl(initConfig, foc));
              }
            catch (ProofInputException e) {
               
               e.printStackTrace();
            }  
         }
      }
   }
     
}
