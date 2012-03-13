package org.key_project.sed.key.core.model;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
public class KeYDebugTarget extends SEDMemoryDebugTarget {
   /**
    * The default name of the only contained {@link ISEDThread}.
    */
   public static final String DEFAULT_THREAD_NAME = "KeY Default Thread";
   
   /**
    * The used model identifier.
    */
   public static final String MODEL_IDENTIFIER = "org.key_project.sed.key.core";
   
   /**
    * The proof in KeY to tread.
    */
   private Proof proof;
   
   /**
    * The only contained child thread.
    */
   private SEDMemoryThread thread;
   
   /**
    * Listens for changes on the auto mode of KeY Main Frame,.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted(e);
      }

      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
   };
   
   /**
    * Maps the KeY instances to the debug API instances.
    */
   private Map<SourceElement, ISEDDebugNode> keyNodeMapping;
   
   /**
    * Constructor.
    * @param launch The parent {@link ILaunch}.
    * @param proof The {@link Proof} in KeY to treat.
    */
   public KeYDebugTarget(ILaunch launch, Proof proof) {
      super(launch);
      // Update references
      Assert.isNotNull(proof);
      this.proof = proof;
      // Update initial model
      setModelIdentifier(MODEL_IDENTIFIER);
      setName(proof.name() != null ? proof.name().toString() : "Unnamed");
      thread = new SEDMemoryThread(getDebugTarget());
      thread.setName(DEFAULT_THREAD_NAME);
      addSymbolicThread(thread);
      keyNodeMapping = new HashMap<SourceElement, ISEDDebugNode>();
      // Observe frozen state of KeY Main Frame
      MainWindow.getInstance().getMediator().addAutoModeListener(autoModeListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !MainWindow.getInstance().frozen; // Only one proof completion per time is possible
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      if (canResume()) {
         // Inform UI that the process is resumed
         super.resume();
         // Run proof
         runProof(proof);
      }
   }
   
   /**
    * Tries to close the given {@link Proof} instance in KeY with
    * the automatic mode.
    * @param proof The {@link Proof} to execute.
    * @throws DebugException Occurred Exception
    */
   protected void runProof(Proof proof) throws DebugException {
       // Make sure that main window is available.
       Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
       MainWindow main = MainWindow.getInstance();
       Assert.isNotNull(main, "KeY main window is not available.");
       // Run proof
       NotificationTask task = null;
       try {
           // Deactivate proof closed dialog
           task = main.getNotificationManager().getNotificationTask(NotificationEventID.PROOF_CLOSED);
           if (task != null) {
               main.getNotificationManager().removeNotificationTask(task);
           }
           // Start interactive proof automatically
           main.getMediator().startAutoMode(proof.openEnabledGoals());
           // Wait for interactive prover
           KeYUtil.waitWhileMainWindowIsFrozen(main);
       }
       finally {
           if (task != null) {
               main.getNotificationManager().addNotificationTask(task);
           }
       }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return super.canSuspend() && 
             MainWindow.getInstance().frozen && // Only if the auto mode is in progress
             MainWindow.getInstance().getMediator().getProof() == proof; // And the auto mode handles this proof
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      if (canSuspend()) {
         MainWindow.getInstance().getMediator().stopAutoMode();
      }
   }

   /**
    * Analyzes the given Proof by printing the executed code in the console.
    * @param proof The Proof to analyze.
    */
   protected void analyzeProof(Proof proof) {
      analyzeNode(proof.root(), 0, thread);
   }

   /**
    * <p>
    * Analyzes the given Proof by printing the executed code in the console.
    * </p>
    * <p>
    * <b>Attention :</b> A correct pruning requires at the moment that
    * the Taclet Option "runtimeExceptions" is set to "runtimeExceptions:allow".
    * Alternatively it is required to modify rule {@code assignment_to_reference_array_component}
    * in file {@code javaRules.key} by uncommenting {@code \add (!(#v=null) & lt(#se, length(#v)) & geq(#se,0) & arrayStoreValid(#v, #se0)==>)}. 
    * </p>
    * @param proof The Proof to analyze.
    */
   protected void analyzeNode(Node node, int level, ISEDDebugNode parentToAddTo) {
      // Analyze node
      if (!node.isClosed()) { // Prune closed branches
         NodeInfo info = node.getNodeInfo();
         SourceElement statement = info.getActiveStatement();
         if (statement != null && statement.getPositionInfo() != null) {
            PositionInfo posInfo = statement.getPositionInfo();
            if (posInfo.getStartPosition() != Position.UNDEFINED) {
               // Add node if not already contained
               ISEDDebugNode debugNode = keyNodeMapping.get(statement);
               if (debugNode == null) {
                  debugNode = createNode(statement, posInfo);
                  addChild(parentToAddTo, debugNode);
                  keyNodeMapping.put(statement, debugNode);
               }
               parentToAddTo = debugNode;
            }
         }
         // Iterate over children
         NodeIterator children = node.childrenIterator();
         while (children.hasNext()) {
            Node child = children.next();
            analyzeNode(child, level + 1, parentToAddTo);
         }
      }
   }
   
   /**
    * Creates a new {@link ISEDDebugNode} for the given {@link SourceElement}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDDebugNode}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDDebugNode}.
    */
   protected ISEDDebugNode createNode(SourceElement statement, PositionInfo posInfo) {
      SEDMemoryStatement newNode = new SEDMemoryStatement(getDebugTarget(), thread, thread);
      newNode.setName(statement.toString());
      if (posInfo.getEndPosition() != null) {
         newNode.setLineNumber(posInfo.getEndPosition().getLine());
      }
      if (posInfo.getFileName() != null) {
         newNode.setSourceName(new File(posInfo.getFileName()).getName());
      }
      return newNode;
   }
   
   /**
    * Adds the child to the parent.
    * @param parent The parent to add to.
    * @param child The child to add.
    */
   protected void addChild(ISEDDebugNode parent, ISEDDebugNode child) {
      if (parent instanceof SEDMemoryThread) {
         ((SEDMemoryThread)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryStatement) {
         ((SEDMemoryStatement)parent).addChild(child);
      }
      else {
         throw new IllegalArgumentException("Unsupported parent \"" + parent + "\".");
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      // Remove proof from user interface
      KeYUtil.removeFromProofList(MainWindow.getInstance(), proof.env());
      // Remove auto mode listener
      MainWindow.getInstance().getMediator().removeAutoModeListener(autoModeListener);
      // Clear cache
      keyNodeMapping.clear();
      // Inform UI that the process is terminated
      super.terminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DebugException {
      // Remove auto mode listener
      MainWindow.getInstance().getMediator().removeAutoModeListener(autoModeListener);
      // Inform UI that the process is disconnected
      super.disconnect();
   }

   /**
    * When the auto mode is started.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      try {
         if (e.getSource() == proof) {
            // Inform UI that the process is resumed
            super.resume();
         }
      }
      catch (DebugException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }

   /**
    * When the auto mode has stopped.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      try {
         if (e.getSource() == proof) {
            // Analyze proof
            analyzeProof(proof);
            // Inform UI that the process is suspended
            super.suspend();
         }
      }
      catch (DebugException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }
}
